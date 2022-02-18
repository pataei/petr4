/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2147.p4
\n
control ingress(inout bit<8> h) {
    action a(inout bit<7> b) {
        h[0:0] = 0;
    }
    apply {
        bit<7> tmp = h[7:1];
        a(tmp);
        h[7:1] = tmp;
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top(ingress()) main;
************************\n******** petr4 type checking result: ********\n************************\n
control ingress(inout bit<8> h) {
  action a(inout bit<7> b) {
    h[0:0] = 0;
  }
  apply {
    bit<7> tmp = h[7:1];
    a(tmp);
    h[7:1] = tmp;
  }
}
control c<H> (inout H h);
package top<H0> (c<H0> c);
top(ingress()) main;

************************\n******** p4c type checking result: ********\n************************\n
