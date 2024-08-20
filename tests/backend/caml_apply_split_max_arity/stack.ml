(* The next few changes are checking that splitting caml_apply does not
   erase local allocations made in a previous region *)
external globalize : local_ 'a -> 'a = "%obj_dup"
external opaque : ('a[@local_opt]) -> ('a[@local_opt]) = "%opaque"

external local_stack_offset : unit -> int = "caml_local_stack_offset"

let rec grow_local_stack n (local_ acc) = exclave_
    let local_ acc = acc +. 1. in
    let local_ acc = if n = 0 then acc else grow_local_stack (n - 1) acc in
    let local_ acc = acc +. 1. in
    acc

let[@inline never] foo (local_ a0) (local_ a1) = exclave_
    let local_ r = a0 +. a1 in
    fun (local_ a2) (local_ a3) a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 a65 a66 a67 a68 a69 a70 a71 a72 a73 a74 a75 a76 a77 a78 a79 a80 a81 a82 a83 a84 a85 a86 a87 a88 a89 a90 a91 a92 a93 a94 a95 a96 a97 a98 a99 a100 a101 a102 a103 a104 a105 a106 a107 a108 a109 a110 a111 a112 a113 a114 a115 a116 a117 a118 a119 a120 a121 a122 a123 a124 a125 a126 a127 a128 a129 a130 a131 a132 a133 a134 a135 a136 a137 a138 a139 a140 a141 a142 a143 a144 a145 a146 a147 a148 a149 a150 a151 a152 a153 a154 a155 a156 a157 a158 a159 a160 a161 a162 a163 a164 a165 a166 a167 a168 a169 a170 a171 a172 a173 a174 a175 a176 a177 a178 a179 a180 a181 a182 a183 a184 a185 a186 a187 a188 a189 a190 a191 a192 a193 a194 a195 a196 a197 a198 a199 a200 a201 a202 a203 a204 a205 a206 a207 a208 a209 a210 a211 a212 a213 a214 a215 a216 a217 a218 a219 a220 a221 a222 a223 a224 a225 a226 a227 a228 a229 a230 a231 a232 a233 a234 a235 a236 a237 a238 a239 a240 a241 a242 a243 a244 a245 a246 a247 a248 a249 a250 a251 a252 a253 a254 a255 a256 ->
    let local_ z = opaque (a2 +. a3) in
    let z = globalize z in
    globalize r +. z +.a4+.a5+.a6+.a7+.a8+.a9+.a10+.a11+.a12+.a13+.a14+.a15+.a16+.a17+.a18+.a19+.a20+.a21+.a22+.a23+.a24+.a25+.a26+.a27+.a28+.a29+.a30+.a31+.a32+.a33+.a34+.a35+.a36+.a37+.a38+.a39+.a40+.a41+.a42+.a43+.a44+.a45+.a46+.a47+.a48+.a49+.a50+.a51+.a52+.a53+.a54+.a55+.a56+.a57+.a58+.a59+.a60+.a61+.a62+.a63+.a64+.a65+.a66+.a67+.a68+.a69+.a70+.a71+.a72+.a73+.a74+.a75+.a76+.a77+.a78+.a79+.a80+.a81+.a82+.a83+.a84+.a85+.a86+.a87+.a88+.a89+.a90+.a91+.a92+.a93+.a94+.a95+.a96+.a97+.a98+.a99+.a100+.a101+.a102+.a103+.a104+.a105+.a106+.a107+.a108+.a109+.a110+.a111+.a112+.a113+.a114+.a115+.a116+.a117+.a118+.a119+.a120+.a121+.a122+.a123+.a124+.a125+.a126+.a127+.a128+.a129+.a130+.a131+.a132+.a133+.a134+.a135+.a136+.a137+.a138+.a139+.a140+.a141+.a142+.a143+.a144+.a145+.a146+.a147+.a148+.a149+.a150+.a151+.a152+.a153+.a154+.a155+.a156+.a157+.a158+.a159+.a160+.a161+.a162+.a163+.a164+.a165+.a166+.a167+.a168+.a169+.a170+.a171+.a172+.a173+.a174+.a175+.a176+.a177+.a178+.a179+.a180+.a181+.a182+.a183+.a184+.a185+.a186+.a187+.a188+.a189+.a190+.a191+.a192+.a193+.a194+.a195+.a196+.a197+.a198+.a199+.a200+.a201+.a202+.a203+.a204+.a205+.a206+.a207+.a208+.a209+.a210+.a211+.a212+.a213+.a214+.a215+.a216+.a217+.a218+.a219+.a220+.a221+.a222+.a223+.a224+.a225+.a226+.a227+.a228+.a229+.a230+.a231+.a232+.a233+.a234+.a235+.a236+.a237+.a238+.a239+.a240+.a241+.a242+.a243+.a244+.a245+.a246+.a247+.a248+.a249+.a250+.a251+.a252+.a253+.a254+.a255+.a256


let[@inline never] g ~(f : local_ float -> local_ float -> local_ float -> local_ float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float -> float) =
    let r = f (local_ 1000000.) (local_ 1.) (local_ 2.) (local_ 3.) 4. 5. 6. 7. 8. 9. 10. 11. 12. 13. 14. 15. 16. 17. 18. 19. 20. 21. 22. 23. 24. 25. 26. 27. 28. 29. 30. 31. 32. 33. 34. 35. 36. 37. 38. 39. 40. 41. 42. 43. 44. 45. 46. 47. 48. 49. 50. 51. 52. 53. 54. 55. 56. 57. 58. 59. 60. 61. 62. 63. 64. 65. 66. 67. 68. 69. 70. 71. 72. 73. 74. 75. 76. 77. 78. 79. 80. 81. 82. 83. 84. 85. 86. 87. 88. 89. 90. 91. 92. 93. 94. 95. 96. 97. 98. 99. 100. 101. 102. 103. 104. 105. 106. 107. 108. 109. 110. 111. 112. 113. 114. 115. 116. 117. 118. 119. 120. 121. 122. 123. 124. 125. 126. 127. 128. 129. 130. 131. 132. 133. 134. 135. 136. 137. 138. 139. 140. 141. 142. 143. 144. 145. 146. 147. 148. 149. 150. 151. 152. 153. 154. 155. 156. 157. 158. 159. 160. 161. 162. 163. 164. 165. 166. 167. 168. 169. 170. 171. 172. 173. 174. 175. 176. 177. 178. 179. 180. 181. 182. 183. 184. 185. 186. 187. 188. 189. 190. 191. 192. 193. 194. 195. 196. 197. 198. 199. 200. 201. 202. 203. 204. 205. 206. 207. 208. 209. 210. 211. 212. 213. 214. 215. 216. 217. 218. 219. 220. 221. 222. 223. 224. 225. 226. 227. 228. 229. 230. 231. 232. 233. 234. 235. 236. 237. 238. 239. 240. 241. 242. 243. 244. 245. 246. 247. 248. 249. 250. 251. 252. 253. 254. 255. 256. in
    r

let _ = grow_local_stack 2000 (local_ 0.)
let x = local_stack_offset ()
let () = print_endline (string_of_float (g ~f:foo))
let y = local_stack_offset ()
let () = print_endline ("unclean local allocs: " ^ string_of_int (y - x))
