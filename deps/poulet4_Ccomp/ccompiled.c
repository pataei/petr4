#include "Petr4Runtime.h"
struct _p_e_t_r_4_0b10010;
struct _p_e_t_r_4_0b1110;
struct _p_e_t_r_4_0b1010;
struct _p_e_t_r_4_0b10010 {
  _Bool _p_e_t_r_4_0b10011;
};

struct _p_e_t_r_4_0b1110 {
  struct BitVec *_p_e_t_r_4_0b1111;
};

struct _p_e_t_r_4_0b1010 {
  _Bool _p_e_t_r_4_0b1011;
};

int main();
_Bool my_compute();
_Bool test_computeChecksum();
_Bool my_verify();
_Bool test_verifyChecksum();
_Bool my_deparser();
_Bool test_deparser();
_Bool my_egress();
_Bool test_egress();
_Bool my_ingress();
_Bool test_ingress();
_Bool my_parser();
_Bool start();
signed char _p_e_t_r_4_0b101000[2] = { 49, 0, };

int main(void)
{
  struct packet_out _p_e_t_r_4_0b111011;
  struct packet_in _p_e_t_r_4_0b111010;
  struct _p_e_t_r_4_0b10010 _p_e_t_r_4_0b111001;
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b111000;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b110111;
  my_parser
    (_p_e_t_r_4_0b111010, &_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000,
     &_p_e_t_r_4_0b111001);
  my_verify(&_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000);
  my_ingress
    (&_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000, &_p_e_t_r_4_0b111001);
  my_egress
    (&_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000, &_p_e_t_r_4_0b111001);
  my_compute(&_p_e_t_r_4_0b110111, &_p_e_t_r_4_0b111000);
  my_deparser(_p_e_t_r_4_0b111011, _p_e_t_r_4_0b110111);
}

_Bool my_compute(struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b110010, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b110100)
{
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b110101;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b110011;
  _p_e_t_r_4_0b110011 = *_p_e_t_r_4_0b110010;
  _p_e_t_r_4_0b110101 = *_p_e_t_r_4_0b110100;
  /*skip*/;
  *_p_e_t_r_4_0b110010 = _p_e_t_r_4_0b110011;
  *_p_e_t_r_4_0b110100 = _p_e_t_r_4_0b110101;
}

_Bool test_computeChecksum(struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b110010, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b110100)
{
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b110101;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b110011;
  _p_e_t_r_4_0b110011 = *_p_e_t_r_4_0b110010;
  _p_e_t_r_4_0b110101 = *_p_e_t_r_4_0b110100;
  *_p_e_t_r_4_0b110010 = _p_e_t_r_4_0b110011;
  *_p_e_t_r_4_0b110100 = _p_e_t_r_4_0b110101;
}

_Bool my_verify(struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b101101, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b101111)
{
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b110000;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b101110;
  _p_e_t_r_4_0b101110 = *_p_e_t_r_4_0b101101;
  _p_e_t_r_4_0b110000 = *_p_e_t_r_4_0b101111;
  /*skip*/;
  *_p_e_t_r_4_0b101101 = _p_e_t_r_4_0b101110;
  *_p_e_t_r_4_0b101111 = _p_e_t_r_4_0b110000;
}

_Bool test_verifyChecksum(struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b101101, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b101111)
{
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b110000;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b101110;
  _p_e_t_r_4_0b101110 = *_p_e_t_r_4_0b101101;
  _p_e_t_r_4_0b110000 = *_p_e_t_r_4_0b101111;
  *_p_e_t_r_4_0b101101 = _p_e_t_r_4_0b101110;
  *_p_e_t_r_4_0b101111 = _p_e_t_r_4_0b110000;
}

_Bool my_deparser(struct packet_out _p_e_t_r_4_0b100100, struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b100101)
{
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b100110;
  _p_e_t_r_4_0b100110 = _p_e_t_r_4_0b100101;
  /*skip*/;
  _p_e_t_r_4_0b100101 = _p_e_t_r_4_0b100110;
}

_Bool test_deparser(struct packet_out _p_e_t_r_4_0b100100, struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b100101)
{
  struct BitVec _p_e_t_r_4_0b101011;
  struct BitVec _p_e_t_r_4_0b101010;
  struct BitVec _p_e_t_r_4_0b101001;
  struct BitVec _p_e_t_r_4_0b100111;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b100110;
  _p_e_t_r_4_0b100110 = _p_e_t_r_4_0b100101;
  init_bitvec(&_p_e_t_r_4_0b100111, 0, 32, _p_e_t_r_4_0b101000);
  init_bitvec(&_p_e_t_r_4_0b101001, 0, 32, _p_e_t_r_4_0b101000);
  interp_bplus
    (&_p_e_t_r_4_0b101010, _p_e_t_r_4_0b100111, _p_e_t_r_4_0b101001);
  _p_e_t_r_4_0b101011 = _p_e_t_r_4_0b101010;
  _p_e_t_r_4_0b100101 = _p_e_t_r_4_0b100110;
}

_Bool my_egress(struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b11101, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b11111, struct _p_e_t_r_4_0b10010 *_p_e_t_r_4_0b100001)
{
  struct _p_e_t_r_4_0b10010 _p_e_t_r_4_0b100010;
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b100000;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b11110;
  _p_e_t_r_4_0b11110 = *_p_e_t_r_4_0b11101;
  _p_e_t_r_4_0b100000 = *_p_e_t_r_4_0b11111;
  _p_e_t_r_4_0b100010 = *_p_e_t_r_4_0b100001;
  /*skip*/;
  *_p_e_t_r_4_0b11101 = _p_e_t_r_4_0b11110;
  *_p_e_t_r_4_0b11111 = _p_e_t_r_4_0b100000;
  *_p_e_t_r_4_0b100001 = _p_e_t_r_4_0b100010;
}

_Bool test_egress(struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b11101, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b11111, struct _p_e_t_r_4_0b10010 *_p_e_t_r_4_0b100001)
{
  struct _p_e_t_r_4_0b10010 _p_e_t_r_4_0b100010;
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b100000;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b11110;
  _p_e_t_r_4_0b11110 = *_p_e_t_r_4_0b11101;
  _p_e_t_r_4_0b100000 = *_p_e_t_r_4_0b11111;
  _p_e_t_r_4_0b100010 = *_p_e_t_r_4_0b100001;
  *_p_e_t_r_4_0b11101 = _p_e_t_r_4_0b11110;
  *_p_e_t_r_4_0b11111 = _p_e_t_r_4_0b100000;
  *_p_e_t_r_4_0b100001 = _p_e_t_r_4_0b100010;
}

_Bool my_ingress(struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b10110, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b11000, struct _p_e_t_r_4_0b10010 *_p_e_t_r_4_0b11010)
{
  struct _p_e_t_r_4_0b10010 _p_e_t_r_4_0b11011;
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b11001;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b10111;
  _p_e_t_r_4_0b10111 = *_p_e_t_r_4_0b10110;
  _p_e_t_r_4_0b11001 = *_p_e_t_r_4_0b11000;
  _p_e_t_r_4_0b11011 = *_p_e_t_r_4_0b11010;
  /*skip*/;
  *_p_e_t_r_4_0b10110 = _p_e_t_r_4_0b10111;
  *_p_e_t_r_4_0b11000 = _p_e_t_r_4_0b11001;
  *_p_e_t_r_4_0b11010 = _p_e_t_r_4_0b11011;
}

_Bool test_ingress(struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b10110, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b11000, struct _p_e_t_r_4_0b10010 *_p_e_t_r_4_0b11010)
{
  struct _p_e_t_r_4_0b10010 _p_e_t_r_4_0b11011;
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b11001;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b10111;
  _p_e_t_r_4_0b10111 = *_p_e_t_r_4_0b10110;
  _p_e_t_r_4_0b11001 = *_p_e_t_r_4_0b11000;
  _p_e_t_r_4_0b11011 = *_p_e_t_r_4_0b11010;
  *_p_e_t_r_4_0b10110 = _p_e_t_r_4_0b10111;
  *_p_e_t_r_4_0b11000 = _p_e_t_r_4_0b11001;
  *_p_e_t_r_4_0b11010 = _p_e_t_r_4_0b11011;
}

_Bool my_parser(struct packet_in _p_e_t_r_4_0b1000, struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b1001, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b1101, struct _p_e_t_r_4_0b10010 *_p_e_t_r_4_0b10001)
{
  struct _p_e_t_r_4_0b10010 _p_e_t_r_4_0b10100;
  struct _p_e_t_r_4_0b1110 _p_e_t_r_4_0b10000;
  struct _p_e_t_r_4_0b1010 _p_e_t_r_4_0b1100;
  _p_e_t_r_4_0b1100 = *_p_e_t_r_4_0b1001;
  _p_e_t_r_4_0b10000 = *_p_e_t_r_4_0b1101;
  _p_e_t_r_4_0b10100 = *_p_e_t_r_4_0b10001;
  start
    (_p_e_t_r_4_0b1000, &_p_e_t_r_4_0b1100, &_p_e_t_r_4_0b10000,
     &_p_e_t_r_4_0b10100);
  *_p_e_t_r_4_0b1001 = _p_e_t_r_4_0b1100;
  *_p_e_t_r_4_0b1101 = _p_e_t_r_4_0b10000;
  *_p_e_t_r_4_0b10001 = _p_e_t_r_4_0b10100;
}

_Bool start(struct packet_in _p_e_t_r_4_0b1000, struct _p_e_t_r_4_0b1010 *_p_e_t_r_4_0b1001, struct _p_e_t_r_4_0b1110 *_p_e_t_r_4_0b1101, struct _p_e_t_r_4_0b10010 *_p_e_t_r_4_0b10001)
{
  /*skip*/;
  return 1;
}

