/petr4/ci-test/type-checking/testdata/p4_16_samples/index.p4
\n
/*
Copyright 2016 VMware, Inc.

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
#include <core.p4>

header H {
    bit<32> field;
}

parser P(packet_in p, out H[2] h) {
    bit<32> x;
    H tmp;
    state start {
        p.extract(tmp);
        transition select (tmp.field) {
            0: n1;
            default: n2;
        }
    }
    state n1 {
        x = 1;
        transition n3;
    }
    state n2 {
        x = 2;
        transition n3;
    }
    state n3 {
        x = x - 1;
        transition n4;
    }
    state n4 {
        p.extract(h[x]);
        transition accept;
    }
}

parser Simple<T>(packet_in p, out T t);
package top<T>(Simple<T> prs);
top(P()) main;
************************\n******** petr4 type checking result: ********\n************************\n
error {
  NoError, PacketTooShort, NoMatch, StackOutOfBounds, HeaderTooShort,
  ParserTimeout, ParserInvalidArgument
}
extern packet_in {
  void extract<T>(out T hdr);
  void extract<T0>(out T0 variableSizeHeader,
                   in bit<32> variableFieldSizeInBits);
  T1 lookahead<T1>();
  void advance(in bit<32> sizeInBits);
  bit<32> length();
}

extern packet_out {
  void emit<T2>(in T2 hdr);
}

extern void verify(in bool check, in error toSignal);
@noWarn("unused")
action NoAction() { 
}
match_kind {
  exact, ternary, lpm
}
header H {
  bit<32> field;
}
parser P(packet_in p, out H[2] h) {
  bit<32> x;
  H tmp;
  state start
    {
    p.extract(tmp);
    transition select(tmp.field) {
      0: n1;
      default: n2;
    }
  }
  state n1 {
    x = 1;
    transition n3;
  }
  state n2 {
    x = 2;
    transition n3;
  }
  state n3 {
    x = x-1;
    transition n4;
  }
  state n4 {
    p.extract(h[x]);
    transition accept;
  }
}
parser Simple<T3> (packet_in p, out T3 t);
package top<T4> (Simple<T4> prs);
top(P()) main;

************************\n******** p4c type checking result: ********\n************************\n
