/petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4
\n
/*
* Copyright 2019, MNK Consulting
* http://mnkcg.com
*
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include <v1model.p4>

typedef bit<48> mac_addr_t;
typedef bit<32>  IPv4Address;

header ethernet_t {
    mac_addr_t dstAddr;
    mac_addr_t srcAddr;
    bit<16>    etherType;
}

// IPv4 header without options
header ipv4_t {
    bit<4>       version;
    bit<4>       ihl;
    bit<8>       diffserv;
    bit<16>      packet_length;
    bit<16>      identification;
    bit<3>       flags;
    bit<13>      fragOffset;
    bit<8>       ttl;
    bit<8>       protocol;
    bit<16>      hdrChecksum;
    IPv4Address  srcAddr;
    IPv4Address  dstAddr;
}

struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
}


struct metadata { }

parser MyParser(packet_in packet, out headers hdr, inout metadata meta,
inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }
}

control MyIngress(inout headers hdr, inout metadata meta,
inout standard_metadata_t standard_metadata) {
    action drop() { mark_to_drop(standard_metadata); }
    action actTbl(bit<24> id, bit<32> ip) {
    }
    table ingress_tbl {
	key = {
	    hdr.ipv4.dstAddr    : exact;
	}
	actions = {actTbl; drop;}
	const default_action = drop;
	const entries = {
	    {(8w0x20++8w0x02++8w0x04++8w0x20)} : actTbl(24w42, (8w0x20++8w0x02++8w0x42++8w0x00));
	}
    }

    apply {
        if (hdr.ipv4.isValid()) {
	    ingress_tbl.apply();
        }
    }
}

control MyEgress(inout headers hdr, inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { }
}

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(),
MyComputeChecksum(), MyDeparser()) main;
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
