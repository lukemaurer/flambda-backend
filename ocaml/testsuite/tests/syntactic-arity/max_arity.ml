(* TEST_BELOW
(* Blank lines added here to preserve locations. *)





*)

(* Observe a case where a function's arity is a different notion
   than native code arity (i.e. the number of arguments required
   to enter the "fast path" where arguments are passed in registers/in
   the argument buffer).

   The max native code arity is 128, but the side-effects here don't run
   until after all 133 arguments are provided.
 *)

let f
  ?x1:(_ = failwith "1")
  ?x2:(_ = failwith "2")
  ?x3:(_ = failwith "3")
  ?x4:(_ = failwith "4")
  ?x5:(_ = failwith "5")
  ?x6:(_ = failwith "6")
  ?x7:(_ = failwith "7")
  ?x8:(_ = failwith "8")
  ?x9:(_ = failwith "9")
  ?x10:(_ = failwith "10")
  ?x11:(_ = failwith "11")
  ?x12:(_ = failwith "12")
  ?x13:(_ = failwith "13")
  ?x14:(_ = failwith "14")
  ?x15:(_ = failwith "15")
  ?x16:(_ = failwith "16")
  ?x17:(_ = failwith "17")
  ?x18:(_ = failwith "18")
  ?x19:(_ = failwith "19")
  ?x20:(_ = failwith "20")
  ?x21:(_ = failwith "21")
  ?x22:(_ = failwith "22")
  ?x23:(_ = failwith "23")
  ?x24:(_ = failwith "24")
  ?x25:(_ = failwith "25")
  ?x26:(_ = failwith "26")
  ?x27:(_ = failwith "27")
  ?x28:(_ = failwith "28")
  ?x29:(_ = failwith "29")
  ?x30:(_ = failwith "30")
  ?x31:(_ = failwith "31")
  ?x32:(_ = failwith "32")
  ?x33:(_ = failwith "33")
  ?x34:(_ = failwith "34")
  ?x35:(_ = failwith "35")
  ?x36:(_ = failwith "36")
  ?x37:(_ = failwith "37")
  ?x38:(_ = failwith "38")
  ?x39:(_ = failwith "39")
  ?x40:(_ = failwith "40")
  ?x41:(_ = failwith "41")
  ?x42:(_ = failwith "42")
  ?x43:(_ = failwith "43")
  ?x44:(_ = failwith "44")
  ?x45:(_ = failwith "45")
  ?x46:(_ = failwith "46")
  ?x47:(_ = failwith "47")
  ?x48:(_ = failwith "48")
  ?x49:(_ = failwith "49")
  ?x50:(_ = failwith "50")
  ?x51:(_ = failwith "51")
  ?x52:(_ = failwith "52")
  ?x53:(_ = failwith "53")
  ?x54:(_ = failwith "54")
  ?x55:(_ = failwith "55")
  ?x56:(_ = failwith "56")
  ?x57:(_ = failwith "57")
  ?x58:(_ = failwith "58")
  ?x59:(_ = failwith "59")
  ?x60:(_ = failwith "60")
  ?x61:(_ = failwith "61")
  ?x62:(_ = failwith "62")
  ?x63:(_ = failwith "63")
  ?x64:(_ = failwith "64")
  ?x65:(_ = failwith "65")
  ?x66:(_ = failwith "66")
  ?x67:(_ = failwith "67")
  ?x68:(_ = failwith "68")
  ?x69:(_ = failwith "69")
  ?x70:(_ = failwith "70")
  ?x71:(_ = failwith "71")
  ?x72:(_ = failwith "72")
  ?x73:(_ = failwith "73")
  ?x74:(_ = failwith "74")
  ?x75:(_ = failwith "75")
  ?x76:(_ = failwith "76")
  ?x77:(_ = failwith "77")
  ?x78:(_ = failwith "78")
  ?x79:(_ = failwith "79")
  ?x80:(_ = failwith "80")
  ?x81:(_ = failwith "81")
  ?x82:(_ = failwith "82")
  ?x83:(_ = failwith "83")
  ?x84:(_ = failwith "84")
  ?x85:(_ = failwith "85")
  ?x86:(_ = failwith "86")
  ?x87:(_ = failwith "87")
  ?x88:(_ = failwith "88")
  ?x89:(_ = failwith "89")
  ?x90:(_ = failwith "90")
  ?x91:(_ = failwith "91")
  ?x92:(_ = failwith "92")
  ?x93:(_ = failwith "93")
  ?x94:(_ = failwith "94")
  ?x95:(_ = failwith "95")
  ?x96:(_ = failwith "96")
  ?x97:(_ = failwith "97")
  ?x98:(_ = failwith "98")
  ?x99:(_ = failwith "99")
  ?x100:(_ = failwith "100")
  ?x101:(_ = failwith "101")
  ?x102:(_ = failwith "102")
  ?x103:(_ = failwith "103")
  ?x104:(_ = failwith "104")
  ?x105:(_ = failwith "105")
  ?x106:(_ = failwith "106")
  ?x107:(_ = failwith "107")
  ?x108:(_ = failwith "108")
  ?x109:(_ = failwith "109")
  ?x110:(_ = failwith "110")
  ?x111:(_ = failwith "111")
  ?x112:(_ = failwith "112")
  ?x113:(_ = failwith "113")
  ?x114:(_ = failwith "114")
  ?x115:(_ = failwith "115")
  ?x116:(_ = failwith "116")
  ?x117:(_ = failwith "117")
  ?x118:(_ = failwith "118")
  ?x119:(_ = failwith "119")
  ?x120:(_ = failwith "120")
  ?x121:(_ = failwith "121")
  ?x122:(_ = failwith "122")
  ?x123:(_ = failwith "123")
  ?x124:(_ = failwith "124")
  ?x125:(_ = failwith "125")
  ?x126:(_ = failwith "126")
  ?x127:(_ = failwith "127")
  ?x128:(_ = failwith "128")
  ?x129:(_ = failwith "129")
  ?x130:(_ = failwith "130")
  ?x131:(_ = failwith "131")
  ()
  () = ();;

let _ = f ();;

print_endline "f (): No exception.";;

try f () () with
| _ -> print_endline "f () (): Exception."
;;

(* TEST
 setup-ocamlopt.byte-build-env;
 ocamlopt.byte;
 check-ocamlopt.byte-output;
 run;
 check-program-output;
*)
