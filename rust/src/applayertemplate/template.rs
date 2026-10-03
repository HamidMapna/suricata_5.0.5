/* Copyright (C) 2018 Open Information Security Foundation
 *
 * You can copy, redistribute or modify this Program under the terms of
 * the GNU General Public License version 2 as published by the Free
 * Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * version 2 along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 */

use std;
use crate::core::{self, ALPROTO_UNKNOWN, AppProto, Flow, IPPROTO_TCP};
use crate::log::*;
use std::mem::transmute;
use crate::applayer::{self, LoggerFlags};
use crate::parser::*;
use std::ffi::CString;
use nom;
use super::parser;
use std::collections::HashSet;

fn opcua_message_type(input: &[u8]) -> &str {
    if input.len() < 3 { return "???"; }
    match &input[0..3] {
        b"HEL" => "HEL", b"ACK" => "ACK", b"OPN" => "OPN", b"MSG" => "MSG", b"CLO" => "CLO", b"ERR" => "ERR", _ => "???",
    }
}

fn opcua_decode_nodeid(input: &[u8], pos: usize)
    -> Option<(OpcUaNodeId, usize)>
{
    if pos >= input.len() {
        return None;
    }

    match input[pos] {
        // TwoByte NodeId
        0x00 => {
            if pos + 2 > input.len() {
                return None;
            }

            let id = input[pos + 1] as u32;

            Some((
                OpcUaNodeId::Numeric {
                    ns: 0,
                    id,
                },
                2,
            ))
        }

        // FourByte NodeId
        0x01 => {
            if pos + 4 > input.len() {
                return None;
            }

            let ns = input[pos + 1] as u16;

            let id = u16::from_le_bytes([
                input[pos + 2],
                input[pos + 3],
            ]) as u32;

            Some((
                OpcUaNodeId::Numeric {
                    ns,
                    id,
                },
                4,
            ))
        }

        // Numeric NodeId
        0x02 => {
            if pos + 7 > input.len() {
                return None;
            }

            let ns = u16::from_le_bytes([
                input[pos + 1],
                input[pos + 2],
            ]);

            let id = u32::from_le_bytes([
                input[pos + 3],
                input[pos + 4],
                input[pos + 5],
                input[pos + 6],
            ]);

            Some((
                OpcUaNodeId::Numeric {
                    ns,
                    id,
                },
                7,
            ))
        }

        // String NodeId
        0x03 => {
            if pos + 7 > input.len() {
                return None;
            }

            let ns = u16::from_le_bytes([
                input[pos + 1],
                input[pos + 2],
            ]);

            let len = i32::from_le_bytes([
                input[pos + 3],
                input[pos + 4],
                input[pos + 5],
                input[pos + 6],
            ]);

            if len < 0 {
                return None;
            }

            let len = len as usize;

            if pos + 7 + len > input.len() {
                return None;
            }

            let id = std::str::from_utf8(
                &input[pos + 7..pos + 7 + len]
            ).ok()?.to_string();

            Some((
                OpcUaNodeId::String {
                    ns,
                    id,
                },
                7 + len,
            ))
        }

        // Guid NodeId
        0x04 => {
            if pos + 19 > input.len() {
                return None;
            }

            let ns = u16::from_le_bytes([
                input[pos + 1],
                input[pos + 2],
            ]);

            let mut id = [0u8; 16];

            id.copy_from_slice(
                &input[pos + 3..pos + 19]
            );

            Some((
                OpcUaNodeId::Guid {
                    ns,
                    id,
                },
                19,
            ))
        }

        // ByteString NodeId
        0x05 => {
            if pos + 7 > input.len() {
                return None;
            }

            let ns = u16::from_le_bytes([
                input[pos + 1],
                input[pos + 2],
            ]);

            let len = i32::from_le_bytes([
                input[pos + 3],
                input[pos + 4],
                input[pos + 5],
                input[pos + 6],
            ]);

            if len < 0 {
                return None;
            }

            let len = len as usize;

            if pos + 7 + len > input.len() {
                return None;
            }

            let mut id = Vec::with_capacity(len);

            id.extend_from_slice(
                &input[pos + 7..pos + 7 + len]
            );

            Some((
                OpcUaNodeId::ByteString {
                    ns,
                    id,
                },
                7 + len,
            ))
        }

        _ => None,
    }
}

fn opcua_skip_string(frame: &[u8], p: &mut usize) -> bool {
    if *p + 4 > frame.len() {
        return false;
    }

    let len = i32::from_le_bytes([
        frame[*p],
        frame[*p + 1],
        frame[*p + 2],
        frame[*p + 3],
    ]);

    *p += 4;

    if len < 0 {
        return true;
    }

    let len = len as usize;

    if *p + len > frame.len() {
        return false;
    }

    *p += len;
    true
}

fn opcua_skip_qualified_name(frame: &[u8], p: &mut usize) -> bool {
    // QualifiedName:
    // UInt16 NamespaceIndex
    // String Name

    if *p + 2 > frame.len() {
        return false;
    }

    *p += 2;

    opcua_skip_string(frame, p)
}

fn opcua_skip_extension_object(frame: &[u8], p: &mut usize) -> bool {
    // TypeId
    if let Some((_, used)) = opcua_decode_nodeid(frame, *p) {
        *p += used;
    } else {
        return false;
    }

    // Encoding byte
    if *p >= frame.len() {
        return false;
    }

    let encoding = frame[*p];
    *p += 1;

    match encoding {
        0x00 => {
            // No body
            true
        }

        0x01 | 0x02 => {
            // ByteString / XML body:
            // Int32 length + body
            if *p + 4 > frame.len() {
                return false;
            }

            let len = i32::from_le_bytes([
                frame[*p],
                frame[*p + 1],
                frame[*p + 2],
                frame[*p + 3],
            ]);

            *p += 4;

            if len < 0 {
                return true;
            }

            let len = len as usize;

            if *p + len > frame.len() {
                return false;
            }

            *p += len;
            true
        }

        _ => false,
    }
}

fn opcua_skip_monitoring_parameters(frame: &[u8], p: &mut usize) -> bool {
    // ClientHandle: UInt32
    if *p + 4 > frame.len() {
        return false;
    }
    *p += 4;

    // SamplingInterval: Double
    if *p + 8 > frame.len() {
        return false;
    }
    *p += 8;

    // Filter: ExtensionObject
    if !opcua_skip_extension_object(frame, p) {
        return false;
    }

    // QueueSize: UInt32
    if *p + 4 > frame.len() {
        return false;
    }
    *p += 4;

    // DiscardOldest: Boolean
    if *p + 1 > frame.len() {
        return false;
    }
    *p += 1;

    true
}

fn opcua_extract_read_request_nodeids(frame: &[u8]) {
    // MSG header = 8 bytes
    // SecureChannelId = 4
    // SecurityTokenId = 4
    // SequenceNumber = 4
    // RequestId = 4
    // ServiceId = 2
    //
    // ServiceId starts at offset 26.
    // RequestHeader starts at offset 28.

    let mut p = 28usize;

    // RequestHeader.AuthenticationToken
    if let Some((nodeid, used)) = opcua_decode_nodeid(frame, p) {
        SCLogNotice!(
            "RUST OPCUA ReadRequest AuthenticationToken {:?} p={}",
            nodeid,
            p
        );
        p += used;
    } else {
        SCLogNotice!(
            "RUST OPCUA ReadRequest AuthenticationToken decode failed p={}",
            p
        );
        return;
    }

    // Timestamp: DateTime = Int64
    if p + 8 > frame.len() {
        return;
    }
    p += 8;

    // RequestHandle: UInt32
    if p + 4 > frame.len() {
        return;
    }
    p += 4;

    // ReturnDiagnostics: UInt32
    if p + 4 > frame.len() {
        return;
    }
    p += 4;

    // AuditEntryId: String
    if !opcua_skip_string(frame, &mut p) {
        SCLogNotice!(
            "RUST OPCUA ReadRequest AuditEntryId decode failed p={}",
            p
        );
        return;
    }

    // TimeoutHint: UInt32
    if p + 4 > frame.len() {
        return;
    }
    p += 4;

    // AdditionalHeader: ExtensionObject
    if !opcua_skip_extension_object(frame, &mut p) {
        SCLogNotice!(
            "RUST OPCUA ReadRequest AdditionalHeader decode failed p={}",
            p
        );
        return;
    }

    // ReadRequest.MaxAge: Double
    if p + 8 > frame.len() {
        SCLogNotice!(
            "RUST OPCUA ReadRequest MaxAge missing p={}",
            p
        );
        return;
    }

    p += 8;

    // ReadRequest.TimestampsToReturn: UInt32
    if p + 4 > frame.len() {
        SCLogNotice!(
            "RUST OPCUA ReadRequest TimestampsToReturn missing p={}",
            p
        );
        return;
    }

    let timestamps_to_return = u32::from_le_bytes([
        frame[p],
        frame[p + 1],
        frame[p + 2],
        frame[p + 3],
    ]);

    p += 4;

    SCLogNotice!(
        "RUST OPCUA ReadRequest TimestampsToReturn={} p={}",
        timestamps_to_return,
        p
    );

    // NodesToRead array length
    if p + 4 > frame.len() {
        SCLogNotice!(
            "RUST OPCUA ReadRequest NodesToRead count missing p={}",
            p
        );
        return;
    }

    let count = i32::from_le_bytes([
        frame[p],
        frame[p + 1],
        frame[p + 2],
        frame[p + 3],
    ]);

    p += 4;

    if count < 0 {
        SCLogNotice!(
            "RUST OPCUA ReadRequest invalid NodesToRead count={} p={}",
            count,
            p
        );
        return;
    }

    let count = count as usize;

    SCLogNotice!(
        "RUST OPCUA ReadRequest NodesToRead={} first_nodeid_p={}",
        count,
        p
    );

    for item_index in 0..count {
        // ---------------------------------------------------------
        // ReadValueId.NodeId
        // ---------------------------------------------------------

        let nodeid_start = p;

        let (nodeid, used) = match opcua_decode_nodeid(frame, p) {
            Some(value) => value,
            None => {
                SCLogNotice!(
                    "RUST OPCUA ReadRequest NodeId decode failed item={} p={}",
                    item_index,
                    p
                );
                return;
            }
        };

        p += used;

        let nodeid_end = p;

        unsafe {
            if OPCUA_NODEIDS.is_none() {
                OPCUA_NODEIDS = Some(HashSet::new());
            }

            if let Some(ref mut nodeids) = OPCUA_NODEIDS {
                nodeids.insert(nodeid.clone());
            }
        }

        SCLogNotice!(
            "RUST OPCUA ReadRequest NODEID item={} p={} {:?}",
            item_index,
            nodeid_start,
            nodeid
        );

        // ---------------------------------------------------------
        // Temporary byte-level trace for item 43
        // ---------------------------------------------------------

        if item_index == 43 {
            SCLogNotice!(
                "RUST OPCUA TRACE item=43 NodeId start={} end={} used={}",
                nodeid_start,
                nodeid_end,
                nodeid_end - nodeid_start
            );

            SCLogNotice!(
                "RUST OPCUA TRACE item=43 NodeId bytes={:02X?}",
                &frame[nodeid_start..nodeid_end]
            );
        }

        // ---------------------------------------------------------
        // AttributeId: UInt32
        // ---------------------------------------------------------

        let attribute_start = p;

        if p + 4 > frame.len() {
            SCLogNotice!(
                "RUST OPCUA ReadRequest AttributeId missing item={} p={}",
                item_index,
                p
            );
            return;
        }

        let attribute_id = u32::from_le_bytes([
            frame[p],
            frame[p + 1],
            frame[p + 2],
            frame[p + 3],
        ]);

        p += 4;

        let attribute_end = p;

        SCLogNotice!(
            "RUST OPCUA ReadRequest AttributeId={} item={} p={}",
            attribute_id,
            item_index,
            p
        );

        if item_index == 43 {
            SCLogNotice!(
                "RUST OPCUA TRACE item=43 AttributeId start={} end={} used=4",
                attribute_start,
                attribute_end
            );

            SCLogNotice!(
                "RUST OPCUA TRACE item=43 AttributeId bytes={:02X?}",
                &frame[attribute_start..attribute_end]
            );
        }

        // ---------------------------------------------------------
        // IndexRange: String
        // ---------------------------------------------------------

        let index_range_start = p;

        if !opcua_skip_string(frame, &mut p) {
            SCLogNotice!(
                "RUST OPCUA ReadRequest IndexRange decode failed item={} p={}",
                item_index,
                p
            );
            return;
        }

        let index_range_end = p;

        if item_index == 43 {
            SCLogNotice!(
                "RUST OPCUA TRACE item=43 IndexRange start={} end={} used={}",
                index_range_start,
                index_range_end,
                index_range_end - index_range_start
            );

            SCLogNotice!(
                "RUST OPCUA TRACE item=43 IndexRange bytes={:02X?}",
                &frame[index_range_start..index_range_end]
            );
        }

        // ---------------------------------------------------------
        // DataEncoding: QualifiedName
        // ---------------------------------------------------------

        let data_encoding_start = p;

        if !opcua_skip_qualified_name(frame, &mut p) {
            SCLogNotice!(
                "RUST OPCUA ReadRequest DataEncoding decode failed item={} p={}",
                item_index,
                p
            );
            return;
        }

        let data_encoding_end = p;

        if item_index == 43 {
            SCLogNotice!(
                "RUST OPCUA TRACE item=43 DataEncoding start={} end={} used={}",
                data_encoding_start,
                data_encoding_end,
                data_encoding_end - data_encoding_start
            );

            SCLogNotice!(
                "RUST OPCUA TRACE item=43 DataEncoding bytes={:02X?}",
                &frame[data_encoding_start..data_encoding_end]
            );

            SCLogNotice!(
                "RUST OPCUA TRACE item=43 TOTAL start={} end={} used={}",
                nodeid_start,
                data_encoding_end,
                data_encoding_end - nodeid_start
            );
        }

        SCLogNotice!(
            "RUST OPCUA ReadRequest after item={} p={}",
            item_index,
            p
        );
    }
}

fn opcua_extract_nodeids(frame: &[u8]) {
    if let Some(pos) = frame.windows(4).position(|w| w == [0x01, 0x00, 0xEF, 0x02]) {
        SCLogNotice!("RUST OPCUA CMI service offset={}", pos);

        let mut p = pos + 4;

        if let Some((_, used)) = opcua_decode_nodeid(frame, p) {
            p += used;
        } else {
            return;
        }

        if p + 8 > frame.len() {
            return;
        }
        p += 8;

        if p + 4 > frame.len() {
            return;
        }
        p += 4;

        if p + 4 > frame.len() {
            return;
        }
        p += 4;

        if p + 4 > frame.len() {
            return;
        }

        let len = i32::from_le_bytes([
            frame[p],
            frame[p + 1],
            frame[p + 2],
            frame[p + 3],
        ]);

        p += 4;

        if len >= 0 {
            let len = len as usize;

            if p + len > frame.len() {
                return;
            }

            p += len;
        }

        if p + 4 > frame.len() {
            return;
        }
        p += 4;

        if let Some((_, used)) = opcua_decode_nodeid(frame, p) {
            p += used;
        } else {
            return;
        }

        if p >= frame.len() {
            return;
        }

        let encoding = frame[p];
        p += 1;

        if encoding != 0x00 {
            if p + 4 > frame.len() {
                return;
            }

            let body_len = i32::from_le_bytes([
                frame[p],
                frame[p + 1],
                frame[p + 2],
                frame[p + 3],
            ]);

            p += 4;

            if body_len < 0 {
                return;
            }

            let body_len = body_len as usize;

            if p + body_len > frame.len() {
                return;
            }

            p += body_len;
        }

        if p + 4 > frame.len() {
            return;
        }

        let subscription_id = u32::from_le_bytes([
            frame[p],
            frame[p + 1],
            frame[p + 2],
            frame[p + 3],
        ]);

        p += 4;

        if p + 4 > frame.len() {
            return;
        }

        let timestamps = u32::from_le_bytes([
            frame[p],
            frame[p + 1],
            frame[p + 2],
            frame[p + 3],
        ]);

        p += 4;

        if p + 4 > frame.len() {
            return;
        }

        let count = i32::from_le_bytes([
            frame[p],
            frame[p + 1],
            frame[p + 2],
            frame[p + 3],
        ]);

        p += 4;

        SCLogNotice!(
            "RUST OPCUA CMI subscription={} timestamps={} items={} nodeid_offset={}",
            subscription_id,
            timestamps,
            count,
            p
        );

        if count < 0 {
            return;
        }

        for item_index in 0..count {
            if let Some((nodeid, used)) = opcua_decode_nodeid(frame, p) {
                SCLogNotice!("RUST OPCUA NODEID {:?}", nodeid);

                unsafe {
                    if OPCUA_NODEIDS.is_none() {
                        OPCUA_NODEIDS = Some(HashSet::new());
                    }

                    if let Some(ref mut nodeids) = OPCUA_NODEIDS {
                        nodeids.insert(nodeid.clone());
                    }
                }

                p += used;
            } else {
                SCLogNotice!(
                    "RUST OPCUA NODEID decode failed item={} p={}",
                    item_index,
                    p
                );
                return;
            }

            if p + 4 > frame.len() {
                return;
            }

            p += 4;

            if p + 4 > frame.len() {
                return;
            }

            let index_range_len = i32::from_le_bytes([
                frame[p],
                frame[p + 1],
                frame[p + 2],
                frame[p + 3],
            ]);

            p += 4;

            if index_range_len >= 0 {
                let len = index_range_len as usize;

                if p + len > frame.len() {
                    return;
                }

                p += len;
            }

            if p + 2 > frame.len() {
                return;
            }

            p += 2;

            if p + 4 > frame.len() {
                return;
            }

            let encoding_name_len = i32::from_le_bytes([
                frame[p],
                frame[p + 1],
                frame[p + 2],
                frame[p + 3],
            ]);

            p += 4;

            if encoding_name_len >= 0 {
                let len = encoding_name_len as usize;

                if p + len > frame.len() {
                    return;
                }

                p += len;
            }

            if p + 4 > frame.len() {
                return;
            }

            p += 4;

             if !opcua_skip_monitoring_parameters(frame, &mut p) {
                SCLogNotice!(
                    "RUST OPCUA MonitoringParameters decode failed item={} p={}",
                    item_index,
                    p
                );
                return;
            }

        }
    }
}

fn opcua_frame_len(input: &[u8]) -> Option<usize> {
    if input.len() < 8 { return None; }
    let len = u32::from_le_bytes([input[4], input[5], input[6], input[7]]) as usize;
    if len < 8 { return None; }
    Some(len)
}

static mut ALPROTO_TEMPLATE: AppProto = ALPROTO_UNKNOWN;

pub struct TemplateTransaction {
    tx_id: u64,
    pub request: Option<String>,
    pub response: Option<String>,

    logged: LoggerFlags,
    de_state: Option<*mut core::DetectEngineState>,
    events: *mut core::AppLayerDecoderEvents,
}

impl TemplateTransaction {
    pub fn new() -> TemplateTransaction {
        TemplateTransaction {
            tx_id: 0,
            request: None,
            response: None,
            logged: LoggerFlags::new(),
            de_state: None,
            events: std::ptr::null_mut(),
        }
    }

    pub fn free(&mut self) {
        if self.events != std::ptr::null_mut() {
            core::sc_app_layer_decoder_events_free_events(&mut self.events);
        }
        if let Some(state) = self.de_state {
            core::sc_detect_engine_state_free(state);
        }
    }
}

impl Drop for TemplateTransaction {
    fn drop(&mut self) {
        self.free();
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum OpcUaNodeId {
    Numeric { ns: u16, id: u32 },
    String { ns: u16, id: String },
    Guid { ns: u16, id: [u8; 16] },
    ByteString { ns: u16, id: Vec<u8> },
}

static mut OPCUA_NODEIDS: Option<HashSet<OpcUaNodeId>> = None;

pub struct TemplateState {
    tx_id: u64,
    request_buffer: Vec<u8>,
    response_buffer: Vec<u8>,
    transactions: Vec<TemplateTransaction>,
}

fn opcua_process_cmi(frame: &[u8]) {
    if frame.windows(4)
        .any(|w| w == [0x01, 0x00, 0xEF, 0x02])
    {
        SCLogNotice!(
            "RUST OPCUA CreateMonitoredItemsRequest detected"
        );

        opcua_extract_nodeids(frame);
    }
}

impl TemplateState {
    pub fn new() -> Self {
        Self {
            tx_id: 0,
            request_buffer: Vec::new(),
            response_buffer: Vec::new(),
            transactions: Vec::new(),
        }
    }

    // Free a transaction by ID.
    fn free_tx(&mut self, tx_id: u64) {
        let len = self.transactions.len();
        let mut found = false;
        let mut index = 0;
        for i in 0..len {
            let tx = &self.transactions[i];
            if tx.tx_id == tx_id + 1 {
                found = true;
                index = i;
                break;
            }
        }
        if found {
            self.transactions.remove(index);
        }
    }

    pub fn get_tx(&mut self, tx_id: u64) -> Option<&TemplateTransaction> {
        for tx in &mut self.transactions {
            if tx.tx_id == tx_id + 1 {
                return Some(tx);
            }
        }
        return None;
    }

    fn new_tx(&mut self) -> TemplateTransaction {
        let mut tx = TemplateTransaction::new();
        self.tx_id += 1;
        tx.tx_id = self.tx_id;
        return tx;
    }

    fn find_request(&mut self) -> Option<&mut TemplateTransaction> {
        for tx in &mut self.transactions {
            if tx.response.is_none() {
                return Some(tx);
            }
        }
        None
    }

    fn parse_request(&mut self, input: &[u8]) -> bool {
        if input.is_empty() {
            return true;
        }

        SCLogNotice!(
            "RUST OPCUA parse_request input_len={}",
            input.len()
        );

        self.request_buffer.extend_from_slice(input);

        loop {
            if self.request_buffer.len() < 8 {
                return true;
            }

            // Find the beginning of an OPC-UA MSG chunk.
            let msg_pos = self.request_buffer
                .windows(4)
                .position(|w| w == b"MSGF");

            let msg_pos = match msg_pos {
                Some(pos) => pos,
                None => {
                    // Keep the last 3 bytes because they could be
                    // the beginning of "MSGF" in the next TCP segment.
                    if self.request_buffer.len() > 3 {
                        let keep_from = self.request_buffer.len() - 3;
                        self.request_buffer.drain(..keep_from);
                    }

                    return true;
                }
            };

            // Discard bytes before MSGF.
            if msg_pos > 0 {
                SCLogNotice!(
                    "RUST OPCUA midstream skipped={} bytes before MSGF",
                    msg_pos
                );

                self.request_buffer.drain(..msg_pos);
            }

            // We now have MSGF at offset zero.
            if self.request_buffer.len() < 8 {
                return true;
            }

            let len = u32::from_le_bytes([
                self.request_buffer[4],
                self.request_buffer[5],
                self.request_buffer[6],
                self.request_buffer[7],
            ]) as usize;

            if len < 8 {
                SCLogNotice!(
                    "RUST OPCUA invalid MSGF length={}",
                    len
                );

                self.request_buffer.drain(..4);
                continue;
            }

            // Complete OPC-UA frame has not arrived yet.
            if self.request_buffer.len() < len {
                return true;
            }

            let frame = self.request_buffer[..len].to_vec();

            let msg_type = opcua_message_type(&frame);
            let chunk_type = frame[3] as char;

            SCLogNotice!(
                "RUST OPCUA REQUEST type={} chunk={} len={}",
                msg_type,
                chunk_type,
                len
            );

            if msg_type == "MSG" {

                // ReadRequest service ID = 0x0277
                if frame.len() >= 28
                    && frame[26] == 0x77
                    && frame[27] == 0x02
                {
                    SCLogNotice!(
                        "RUST OPCUA ReadRequest detected service_offset=26"
                    );

                    opcua_extract_read_request_nodeids(&frame);
                }

                // CreateMonitoredItemsRequest
                opcua_process_cmi(&frame);

                let dump_len = std::cmp::min(len, 200);
                let mut hex = String::new();

                for &b in &frame[..dump_len] {
                    hex.push_str(&format!("{:02X} ", b));
                }

                SCLogNotice!(
                    "RUST OPCUA MSG REQUEST len={} dump={} bytes={}",
                    len,
                    dump_len,
                    hex
                );
            }

            let mut tx = self.new_tx();
            tx.request = Some(format!("{} len={}", msg_type, len));
            self.transactions.push(tx);

            // Remove the complete OPC-UA frame.
            self.request_buffer.drain(..len);
        }

        true
    }

    fn parse_response(&mut self, input: &[u8]) -> bool {
        // We're not interested in empty responses.
        if input.len() == 0 {
            return true;
        }

        // For simplicity, always extend the buffer and work on it.
        self.response_buffer.extend(input);

        let tmp: Vec<u8>;
        let mut current = {
            tmp = self.response_buffer.split_off(0);
            tmp.as_slice()
        };

        while current.len() > 0 {
            match opcua_frame_len(current) {
                Some(len) if current.len() >= len => {
                    let frame = &current[..len];
                    let msg_type = opcua_message_type(frame);
                    let chunk_type = frame[3] as char;

                    SCLogNotice!(
                        "RUST OPCUA RESPONSE type={} chunk={} len={}",
                        msg_type,
                        chunk_type,
                        len
                    );

                    if msg_type == "MSG" {
                        let dump_len = std::cmp::min(len, 200);
                        let mut hex = String::new();
                        opcua_process_cmi(&frame);
                        for &b in &frame[..dump_len] {
                            hex.push_str(&format!("{:02X} ", b));
                        }

                        SCLogNotice!(
                            "RUST OPCUA MSG RESPONSE len={} dump={} bytes={}",
                            len,
                            dump_len,
                            hex
                        );
                    }                         

                    current = &current[len..];
                    match self.find_request() {
                        Some(tx) => {
                            tx.response = Some(format!("{} len={}", msg_type, len));
                            SCLogNotice!("Found response for request:");
                            SCLogNotice!("- Request: {:?}", tx.request);
                            SCLogNotice!("- Response: {:?}", tx.response);
                        }
                        None => {}
                    }
                }
                Some(_) | None => {
                    self.response_buffer.extend_from_slice(current);
                    break;
                }
            }
        }

        return true;
    }

    fn tx_iterator(
        &mut self,
        min_tx_id: u64,
        state: &mut u64,
    ) -> Option<(&TemplateTransaction, u64, bool)> {
        let mut index = *state as usize;
        let len = self.transactions.len();

        while index < len {
            let tx = &self.transactions[index];
            if tx.tx_id < min_tx_id + 1 {
                index += 1;
                continue;
            }
            *state = index as u64;
            return Some((tx, tx.tx_id - 1, (len - index) > 1));
        }

        return None;
    }
}

/// Probe to see if this input looks like a request or response.
///
/// For the purposes of this template things will be kept simple. The
/// protocol is text based with the leading text being the length of
/// the message in bytes. So simply make sure the first character is
/// between "1" and "9".
fn probe(input: &[u8]) -> bool {
    // OPC-UA HEL
    if input.len() >= 3
        && input[0] == b'H'
        && input[1] == b'E'
        && input[2] == b'L'
    {
        return true;
    }

    // OPC-UA MSG, first chunk
    if input.len() >= 8
        && input[0] == b'M'
        && input[1] == b'S'
        && input[2] == b'G'
        && input[3] == b'F'
    {
        let msg_len = u32::from_le_bytes([
            input[4],
            input[5],
            input[6],
            input[7],
        ]) as usize;

        if msg_len >= 8 {
            return true;
        }
    }

   return false;
}

export_tx_get_detect_state!(
    rs_template_tx_get_detect_state,
    TemplateTransaction
);
export_tx_set_detect_state!(
    rs_template_tx_set_detect_state,
    TemplateTransaction
);

/// C entry point for a probing parser.
#[no_mangle]
pub extern "C" fn rs_template_probing_parser(
    _flow: *const Flow,
    _direction: u8,
    input: *const u8,
    input_len: u32,
    _rdir: *mut u8
) -> AppProto {
    SCLogNotice!("RUST PROBE called input_len={}", input_len);
    // Need at least 2 bytes.
    if input_len > 1 && input != std::ptr::null_mut() {
        let slice = build_slice!(input, input_len as usize);
        if probe(slice) {
            return unsafe { ALPROTO_TEMPLATE };
        }
    }
    return ALPROTO_UNKNOWN;
}

#[no_mangle]
pub extern "C" fn rs_template_state_new() -> *mut std::os::raw::c_void {
    let state = TemplateState::new();
    let boxed = Box::new(state);
    return unsafe { transmute(boxed) };
}

#[no_mangle]
pub extern "C" fn rs_template_state_free(state: *mut std::os::raw::c_void) {
    // Just unbox...
    let _drop: Box<TemplateState> = unsafe { transmute(state) };
}

#[no_mangle]
pub extern "C" fn rs_template_state_tx_free(
    state: *mut std::os::raw::c_void,
    tx_id: u64,
) {
    let state = cast_pointer!(state, TemplateState);
    state.free_tx(tx_id);
}

#[no_mangle]
pub extern "C" fn rs_template_parse_request(
    _flow: *const Flow,
    state: *mut std::os::raw::c_void,
    pstate: *mut std::os::raw::c_void,
    input: *const u8,
    input_len: u32,
    _data: *const std::os::raw::c_void,
    _flags: u8,
) -> i32 {
    let eof = unsafe {
        if AppLayerParserStateIssetFlag(pstate, APP_LAYER_PARSER_EOF) > 0 {
            true
        } else {
            false
        }
    };

    if eof {
        // If needed, handled EOF, or pass it into the parser.
    }

    let state = cast_pointer!(state, TemplateState);
    let buf = build_slice!(input, input_len as usize);
    if state.parse_request(buf) {
        return 1;
    }
    return -1;
}

#[no_mangle]
pub extern "C" fn rs_template_parse_response(
    _flow: *const Flow,
    state: *mut std::os::raw::c_void,
    pstate: *mut std::os::raw::c_void,
    input: *const u8,
    input_len: u32,
    _data: *const std::os::raw::c_void,
    _flags: u8,
) -> i32 {
    let _eof = unsafe {
        if AppLayerParserStateIssetFlag(pstate, APP_LAYER_PARSER_EOF) > 0 {
            true
        } else {
            false
        }
    };
    let state = cast_pointer!(state, TemplateState);
    let buf = build_slice!(input, input_len as usize);
    if state.parse_response(buf) {
        return 1;
    }
    return -1;
}

#[no_mangle]
pub extern "C" fn rs_template_state_get_tx(
    state: *mut std::os::raw::c_void,
    tx_id: u64,
) -> *mut std::os::raw::c_void {
    let state = cast_pointer!(state, TemplateState);
    match state.get_tx(tx_id) {
        Some(tx) => {
            return unsafe { transmute(tx) };
        }
        None => {
            return std::ptr::null_mut();
        }
    }
}

#[no_mangle]
pub extern "C" fn rs_template_state_get_tx_count(
    state: *mut std::os::raw::c_void,
) -> u64 {
    let state = cast_pointer!(state, TemplateState);
    return state.tx_id;
}

#[no_mangle]
pub extern "C" fn rs_template_state_progress_completion_status(
    _direction: u8,
) -> std::os::raw::c_int {
    // This parser uses 1 to signal transaction completion status.
    return 1;
}

#[no_mangle]
pub extern "C" fn rs_template_tx_get_alstate_progress(
    tx: *mut std::os::raw::c_void,
    _direction: u8,
) -> std::os::raw::c_int {
    let tx = cast_pointer!(tx, TemplateTransaction);

    // Transaction is done if we have a response.
    if tx.response.is_some() {
        return 1;
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_template_tx_get_logged(
    _state: *mut std::os::raw::c_void,
    tx: *mut std::os::raw::c_void,
) -> u32 {
    let tx = cast_pointer!(tx, TemplateTransaction);
    return tx.logged.get();
}

#[no_mangle]
pub extern "C" fn rs_template_tx_set_logged(
    _state: *mut std::os::raw::c_void,
    tx: *mut std::os::raw::c_void,
    logged: u32,
) {
    let tx = cast_pointer!(tx, TemplateTransaction);
    tx.logged.set(logged);
}

#[no_mangle]
pub extern "C" fn rs_template_state_get_events(
    tx: *mut std::os::raw::c_void
) -> *mut core::AppLayerDecoderEvents {
    let tx = cast_pointer!(tx, TemplateTransaction);
    return tx.events;
}

#[no_mangle]
pub extern "C" fn rs_template_state_get_event_info(
    _event_name: *const std::os::raw::c_char,
    _event_id: *mut std::os::raw::c_int,
    _event_type: *mut core::AppLayerEventType,
) -> std::os::raw::c_int {
    return -1;
}

#[no_mangle]
pub extern "C" fn rs_template_state_get_event_info_by_id(_event_id: std::os::raw::c_int,
                                                         _event_name: *mut *const std::os::raw::c_char,
                                                         _event_type: *mut core::AppLayerEventType
) -> i8 {
    return -1;
}
#[no_mangle]
pub extern "C" fn rs_template_state_get_tx_iterator(
    _ipproto: u8,
    _alproto: AppProto,
    state: *mut std::os::raw::c_void,
    min_tx_id: u64,
    _max_tx_id: u64,
    istate: &mut u64,
) -> applayer::AppLayerGetTxIterTuple {
    let state = cast_pointer!(state, TemplateState);
    match state.tx_iterator(min_tx_id, istate) {
        Some((tx, out_tx_id, has_next)) => {
            let c_tx = unsafe { transmute(tx) };
            let ires = applayer::AppLayerGetTxIterTuple::with_values(
                c_tx,
                out_tx_id,
                has_next,
            );
            return ires;
        }
        None => {
            return applayer::AppLayerGetTxIterTuple::not_found();
        }
    }
}

/// Get the request buffer for a transaction from C.
///
/// No required for parsing, but an example function for retrieving a
/// pointer to the request buffer from C for detection.
#[no_mangle]
pub extern "C" fn rs_template_get_request_buffer(
    tx: *mut std::os::raw::c_void,
    buf: *mut *const u8,
    len: *mut u32,
) -> u8
{
    let tx = cast_pointer!(tx, TemplateTransaction);
    if let Some(ref request) = tx.request {
        if request.len() > 0 {
            unsafe {
                *len = request.len() as u32;
                *buf = request.as_ptr();
            }
            return 1;
        }
    }
    return 0;
}

/// Get the response buffer for a transaction from C.
#[no_mangle]
pub extern "C" fn rs_template_get_response_buffer(
    tx: *mut std::os::raw::c_void,
    buf: *mut *const u8,
    len: *mut u32,
) -> u8
{
    let tx = cast_pointer!(tx, TemplateTransaction);
    if let Some(ref response) = tx.response {
        if response.len() > 0 {
            unsafe {
                *len = response.len() as u32;
                *buf = response.as_ptr();
            }
            return 1;
        }
    }
    return 0;
}

// Parser name as a C style string.
const PARSER_NAME: &'static [u8] = b"template-rust\0";

#[no_mangle]
pub unsafe extern "C" fn rs_template_register_parser() {
    let default_port = CString::new("[4840]").unwrap();
    let parser = RustParser {
        name: PARSER_NAME.as_ptr() as *const std::os::raw::c_char,
        default_port: default_port.as_ptr(),
        ipproto: IPPROTO_TCP,
        probe_ts: rs_template_probing_parser,
        probe_tc: rs_template_probing_parser,
        min_depth: 0,
        max_depth: 16,
        state_new: rs_template_state_new,
        state_free: rs_template_state_free,
        tx_free: rs_template_state_tx_free,
        parse_ts: rs_template_parse_request,
        parse_tc: rs_template_parse_response,
        get_tx_count: rs_template_state_get_tx_count,
        get_tx: rs_template_state_get_tx,
        tx_get_comp_st: rs_template_state_progress_completion_status,
        tx_get_progress: rs_template_tx_get_alstate_progress,
        get_tx_logged: Some(rs_template_tx_get_logged),
        set_tx_logged: Some(rs_template_tx_set_logged),
        get_de_state: rs_template_tx_get_detect_state,
        set_de_state: rs_template_tx_set_detect_state,
        get_events: Some(rs_template_state_get_events),
        get_eventinfo: Some(rs_template_state_get_event_info),
        get_eventinfo_byid : Some(rs_template_state_get_event_info_by_id),
        localstorage_new: None,
        localstorage_free: None,
        get_tx_mpm_id: None,
        set_tx_mpm_id: None,
        get_files: None,
        get_tx_iterator: Some(rs_template_state_get_tx_iterator),
        get_tx_detect_flags: None,
        set_tx_detect_flags: None,
        flags: 0,
    };

    let ip_proto_str = CString::new("tcp").unwrap();

    if AppLayerProtoDetectConfProtoDetectionEnabled(
        ip_proto_str.as_ptr(),
        parser.name,
    ) != 0
    {
        let alproto = AppLayerRegisterProtocolDetection(&parser, 1);
        ALPROTO_TEMPLATE = alproto;
        if AppLayerParserConfParserEnabled(
            ip_proto_str.as_ptr(),
            parser.name,
        ) != 0
        {
            let _ = AppLayerRegisterParser(&parser, alproto);
        }
        SCLogNotice!("Rust template parser registered.");
    } else {
        SCLogNotice!("Protocol detector and parser disabled for TEMPLATE.");
    }
}
