#!/bin/sh

touch /usr/suricata_5.0.5/rust/src/applayertemplate/template.rs

cd /usr/suricata_5.0.5/rust || exit 1
cargo build --release --offline --features "lua" || exit 1

cd /usr/suricata_5.0.5/src || exit 1
gmake -B suricata || exit 1

./.libs/suricata -r /tmp/7-Nodes-string-numeric.pcapng -k none | grep -E 'RUST PROBE|RUST GETPROTO|RUST OPCUA'