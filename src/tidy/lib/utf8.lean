import data.num.bitwise
import data.nat.cast
import .num

namespace utf8

def TAG_CONT    := 0b10000000
def TAG_TWO_B   := 0b11000000
def TAG_THREE_B := 0b11100000
def TAG_FOUR_B  := 0b11110000
def MAX_ONE_B   := 0x80
def MAX_TWO_B   := 0x800
def MAX_THREE_B := 0x10000

open num

def decode_char (c : char) : list char :=
  let code : nat := c.to_nat in
  let bytes : list ℕ :=
    if code < MAX_ONE_B then [
      code
    ]
    else if code < MAX_TWO_B then [
      lor (land (shiftr code  6) 0x1F) TAG_TWO_B,
      lor (land (shiftr code  0) 0x3F) TAG_CONT
    ]
    else if code < MAX_THREE_B then [
      lor (land (shiftr code 12) 0x0F) TAG_THREE_B,
      lor (land (shiftr code  6) 0x3F) TAG_CONT,
      lor (land (shiftr code  0) 0x3F) TAG_CONT
    ]
    else [
      lor (land (shiftr code 18) 0x07) TAG_FOUR_B,
      lor (land (shiftr code 12) 0x3F) TAG_CONT,
      lor (land (shiftr code  6) 0x3F) TAG_CONT,
      lor (land (shiftr code  0) 0x3F) TAG_CONT
    ]
  in
  bytes.map nat.trunc_to_char

def decode_aux : list char → list char → list char
| p []       := p
| p (c :: r) := decode_aux (p.append (decode_char c)) r

def decode (cb : list char) : list char := decode_aux [] cb

end utf8