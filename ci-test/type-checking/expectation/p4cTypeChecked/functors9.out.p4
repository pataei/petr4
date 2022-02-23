/petr4/ci-test/type-checking/testdata/p4_16_samples/functors9.p4
\n
/*
Copyright 2013-present Barefoot Networks, Inc.

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

extern e<T> {
    e();
    T get();
}

parser p1<T>(in T a) {
    e<T>() ei;
    state start {
        T w = ei.get();
        transition accept;
    }
}

parser simple(in bit<2> a);

package m(simple n);

m(p1<bit<2>>()) main;
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n