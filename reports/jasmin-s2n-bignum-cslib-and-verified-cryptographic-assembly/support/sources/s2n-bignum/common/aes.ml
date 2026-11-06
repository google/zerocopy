(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* install_user_printer("pp_print_num",pp_print_num_hex);; *)

(* ========================================================================= *)
(* Word operation helpers                                                    *)
(* ========================================================================= *)

let word_join_list_16_128 = new_definition
  `word_join_list_16_128 (lst:((128) word) list) : (2048) word =
  ((word_join:128 word->1920 word->2048 word) (EL 0 lst)
    ((word_join:128 word->1792 word->1920 word) (EL 1 lst)
     ((word_join:128 word->1664 word->1792 word) (EL 2 lst)
      ((word_join:128 word->1536 word->1664 word) (EL 3 lst)
       ((word_join:128 word->1408 word->1536 word) (EL 4 lst)
        ((word_join:128 word->1280 word->1408 word) (EL 5 lst)
         ((word_join:128 word->1152 word->1280 word) (EL 6 lst)
          ((word_join:128 word->1024 word->1152 word) (EL 7 lst)
           ((word_join:128 word->896 word->1024 word) (EL 8 lst)
            ((word_join:128 word->768 word->896 word) (EL 9 lst)
             ((word_join:128 word->640 word->768 word) (EL 10 lst)
              ((word_join:128 word->512 word->640 word) (EL 11 lst)
               ((word_join:128 word->384 word->512 word) (EL 12 lst)
                ((word_join:128 word->256 word->384 word) (EL 13 lst)
                 ((word_join:128 word->128 word->256 word) (EL 14 lst)
                  (EL 15 lst))))))))))))))))`;;

let word_join_list_16_8 = new_definition
  `word_join_list_16_8 (lst:((8) word) list) : (128) word =
  ((word_join:8 word->120 word->128 word) (EL 0 lst)
    ((word_join:8 word->112 word->120 word) (EL 1 lst)
     ((word_join:8 word->104 word->112 word) (EL 2 lst)
      ((word_join:8 word->96 word->104 word) (EL 3 lst)
       ((word_join:8 word->88 word->96 word) (EL 4 lst)
        ((word_join:8 word->80 word->88 word) (EL 5 lst)
         ((word_join:8 word->72 word->80 word) (EL 6 lst)
          ((word_join:8 word->64 word->72 word) (EL 7 lst)
           ((word_join:8 word->56 word->64 word) (EL 8 lst)
            ((word_join:8 word->48 word->56 word) (EL 9 lst)
             ((word_join:8 word->40 word->48 word) (EL 10 lst)
              ((word_join:8 word->32 word->40 word) (EL 11 lst)
               ((word_join:8 word->24 word->32 word) (EL 12 lst)
                ((word_join:8 word->16 word->24 word) (EL 13 lst)
                 ((word_join:8 word->8 word->16 word) (EL 14 lst)
                  (EL 15 lst))))))))))))))))`;;


(* ========================================================================= *)
(* Constant tables                                                           *)
(* ========================================================================= *)

(* GF2 *)
let GF2 = new_definition `GF2:((128)word) list =
  [ word 0x16bb54b00f2d99416842e6bf0d89a18c
  ; word 0xdf2855cee9871e9b948ed9691198f8e1
  ; word 0x9e1dc186b95735610ef6034866b53e70
  ; word 0x8a8bbd4b1f74dde8c6b4a61c2e2578ba
  ; word 0x08ae7a65eaf4566ca94ed58d6d37c8e7
  ; word 0x79e4959162acd3c25c2406490a3a32e0
  ; word 0xdb0b5ede14b8ee4688902a22dc4f8160
  ; word 0x73195d643d7ea7c41744975fec130ccd
  ; word 0xd2f3ff1021dab6bcf5389d928f40a351
  ; word 0xa89f3c507f02f94585334d43fbaaefd0
  ; word 0xcf584c4a39becb6a5bb1fc20ed00d153
  ; word 0x842fe329b3d63b52a05a6e1b1a2c8309
  ; word 0x75b227ebe28012079a059618c323c704
  ; word 0x1531d871f1e5a534ccf73f362693fdb7
  ; word 0xc072a49cafa2d4adf04759fa7dc982ca
  ; word 0x76abd7fe2b670130c56f6bf27b777c63
  ]`;;

let joined_GF2 = new_definition `joined_GF2:(2048)word =
  word_join_list_16_128 GF2`;;

(* GF2_inv *)
let GF2_inv = new_definition `GF2_inv:((128)word) list =
  [ word 0x7d0c2155631469e126d677ba7e042b17
  ; word 0x619953833cbbebc8b0f52aae4d3be0a0
  ; word 0xef9cc9939f7ae52d0d4ab519a97f5160
  ; word 0x5fec8027591012b131c7078833a8dd1f
  ; word 0xf45acd78fec0db9a2079d2c64b3e56fc
  ; word 0x1bbe18aa0e62b76f89c5291d711af147
  ; word 0x6edf751ce837f9e28535ade72274ac96
  ; word 0x73e6b4f0cecff297eadc674f4111913a
  ; word 0x6b8a130103bdafc1020f3fca8f1e2cd0
  ; word 0x0645b3b80558e4f70ad3bc8c00abd890
  ; word 0x849d8da75746155edab9edfd5048706c
  ; word 0x92b6655dcc5ca4d41698688664f6f872
  ; word 0x25d18b6d49a25b76b224d92866a12e08
  ; word 0x4ec3fa420b954cee3d23c2a632947b54
  ; word 0xcbe9dec444438e3487ff2f9b8239e37c
  ; word 0xfbd7f3819ea340bf38a53630d56a0952
  ]`;;

let joined_GF2_inv = new_definition `joined_GF2_inv:(2048)word =
  word_join_list_16_128 GF2_inv`;;

(* FFmul tables *)
let FFmul_02 = new_definition `FFmul_02:(((128)word) list) = [
    word 0xE5E7E1E3EDEFE9EBF5F7F1F3FDFFF9FB
  ; word 0xC5C7C1C3CDCFC9CBD5D7D1D3DDDFD9DB
  ; word 0xA5A7A1A3ADAFA9ABB5B7B1B3BDBFB9BB
  ; word 0x858781838D8F898B959791939D9F999B
  ; word 0x656761636D6F696B757771737D7F797B
  ; word 0x454741434D4F494B555751535D5F595B
  ; word 0x252721232D2F292B353731333D3F393B
  ; word 0x050701030D0F090B151711131D1F191B
  ; word 0xFEFCFAF8F6F4F2F0EEECEAE8E6E4E2E0
  ; word 0xDEDCDAD8D6D4D2D0CECCCAC8C6C4C2C0
  ; word 0xBEBCBAB8B6B4B2B0AEACAAA8A6A4A2A0
  ; word 0x9E9C9A98969492908E8C8A8886848280
  ; word 0x7E7C7A78767472706E6C6A6866646260
  ; word 0x5E5C5A58565452504E4C4A4846444240
  ; word 0x3E3C3A38363432302E2C2A2826242220
  ; word 0x1E1C1A18161412100E0C0A0806040200 ]`;;

let joined_FFmul_02 = new_definition `joined_FFmul_02:2048 word =
  word_join_list_16_128 FFmul_02`;;

let FFmul_03 = new_definition `FFmul_03:(((128)word) list) = [
    word 0x1A191C1F16151013020104070E0D080B
  ; word 0x2A292C2F26252023323134373E3D383B
  ; word 0x7A797C7F76757073626164676E6D686B
  ; word 0x4A494C4F46454043525154575E5D585B
  ; word 0xDAD9DCDFD6D5D0D3C2C1C4C7CECDC8CB
  ; word 0xEAE9ECEFE6E5E0E3F2F1F4F7FEFDF8FB
  ; word 0xBAB9BCBFB6B5B0B3A2A1A4A7AEADA8AB
  ; word 0x8A898C8F86858083929194979E9D989B
  ; word 0x818287848D8E8B88999A9F9C95969390
  ; word 0xB1B2B7B4BDBEBBB8A9AAAFACA5A6A3A0
  ; word 0xE1E2E7E4EDEEEBE8F9FAFFFCF5F6F3F0
  ; word 0xD1D2D7D4DDDEDBD8C9CACFCCC5C6C3C0
  ; word 0x414247444D4E4B48595A5F5C55565350
  ; word 0x717277747D7E7B78696A6F6C65666360
  ; word 0x212227242D2E2B28393A3F3C35363330
  ; word 0x111217141D1E1B18090A0F0C05060300 ]`;;

let joined_FFmul_03 = new_definition `joined_FFmul_03:2048 word =
  word_join_list_16_128 FFmul_03`;;

let FFmul_09 = new_definition `FFmul_09:(((128)word) list) = [
    word 0x464F545D626B70790E071C152A233831
  ; word 0xD6DFC4CDF2FBE0E99E978C85BAB3A8A1
  ; word 0x7D746F6659504B42353C272E1118030A
  ; word 0xEDE4FFF6C9C0DBD2A5ACB7BE8188939A
  ; word 0x3039222B141D060F78716A635C554E47
  ; word 0xA0A9B2BB848D969FE8E1FAF3CCC5DED7
  ; word 0x0B0219102F263D34434A5158676E757C
  ; word 0x9B928980BFB6ADA4D3DAC1C8F7FEE5EC
  ; word 0xAAA3B8B18E879C95E2EBF0F9C6CFD4DD
  ; word 0x3A3328211E170C05727B6069565F444D
  ; word 0x9198838AB5BCA7AED9D0CBC2FDF4EFE6
  ; word 0x0108131A252C373E49405B526D647F76
  ; word 0xDCD5CEC7F8F1EAE3949D868FB0B9A2AB
  ; word 0x4C455E5768617A73040D161F2029323B
  ; word 0xE7EEF5FCC3CAD1D8AFA6BDB48B829990
  ; word 0x777E656C535A41483F362D241B120900 ]`;;

let joined_FFmul_09 = new_definition `joined_FFmul_09:2048 word =
  word_join_list_16_128 FFmul_09`;;

let FFmul_0B = new_definition `FFmul_0B:(((128)word) list) = [
    word 0xA3A8B5BE8F849992FBF0EDE6D7DCC1CA
  ; word 0x1318050E3F3429224B405D56676C717A
  ; word 0xD8D3CEC5F4FFE2E9808B969DACA7BAB1
  ; word 0x68637E75444F5259303B262D1C170A01
  ; word 0x555E434879726F640D061B10212A373C
  ; word 0xE5EEF3F8C9C2DFD4BDB6ABA0919A878C
  ; word 0x2E2538330209141F767D606B5A514C47
  ; word 0x9E958883B2B9A4AFC6CDD0DBEAE1FCF7
  ; word 0x545F424978736E650C071A11202B363D
  ; word 0xE4EFF2F9C8C3DED5BCB7AAA1909B868D
  ; word 0x2F2439320308151E777C616A5B504D46
  ; word 0x9F948982B3B8A5AEC7CCD1DAEBE0FDF6
  ; word 0xA2A9B4BF8E859893FAF1ECE7D6DDC0CB
  ; word 0x1219040F3E3528234A415C57666D707B
  ; word 0xD9D2CFC4F5FEE3E8818A979CADA6BBB0
  ; word 0x69627F74454E5358313A272C1D160B00 ]`;;

let joined_FFmul_0B = new_definition `joined_FFmul_0B:2048 word =
  word_join_list_16_128 FFmul_0B`;;

let FFmul_0D = new_definition `FFmul_0D:(((128)word) list) = [
    word 0x979A8D80A3AEB9B4FFF2E5E8CBC6D1DC
  ; word 0x474A5D50737E69642F2235381B16010C
  ; word 0x2C21363B1815020F44495E53707D6A67
  ; word 0xFCF1E6EBC8C5D2DF94998E83A0ADBAB7
  ; word 0xFAF7E0EDCEC3D4D9929F8885A6ABBCB1
  ; word 0x2A27303D1E130409424F5855767B6C61
  ; word 0x414C5B5675786F622924333E1D10070A
  ; word 0x919C8B86A5A8BFB2F9F4E3EECDC0D7DA
  ; word 0x4D40575A7974636E25283F32111C0B06
  ; word 0x9D90878AA9A4B3BEF5F8EFE2C1CCDBD6
  ; word 0xF6FBECE1C2CFD8D59E938489AAA7B0BD
  ; word 0x262B3C31121F08054E4354597A77606D
  ; word 0x202D3A3714190E034845525F7C71666B
  ; word 0xF0FDEAE7C4C9DED39895828FACA1B6BB
  ; word 0x9B96818CAFA2B5B8F3FEE9E4C7CADDD0
  ; word 0x4B46515C7F726568232E3934171A0D00 ]`;;

let joined_FFmul_0D = new_definition `joined_FFmul_0D:2048 word =
  word_join_list_16_128 FFmul_0D`;;

let FFmul_0E = new_definition `FFmul_0E:(((128)word) list) = [
    word 0x8D83919FB5BBA9A7FDF3E1EFC5CBD9D7
  ; word 0x6D63717F555B49471D13010F252B3937
  ; word 0x56584A446E60727C26283A341E10020C
  ; word 0xB6B8AAA48E80929CC6C8DAD4FEF0E2EC
  ; word 0x202E3C321816040A505E4C426866747A
  ; word 0xC0CEDCD2F8F6E4EAB0BEACA28886949A
  ; word 0xFBF5E7E9C3CDDFD18B859799B3BDAFA1
  ; word 0x1B150709232D3F316B657779535D4F41
  ; word 0xCCC2D0DEF4FAE8E6BCB2A0AE848A9896
  ; word 0x2C22303E141A08065C52404E646A7876
  ; word 0x17190B052F21333D67697B755F51434D
  ; word 0xF7F9EBE5CFC1D3DD87899B95BFB1A3AD
  ; word 0x616F7D735957454B111F0D032927353B
  ; word 0x818F9D93B9B7A5ABF1FFEDE3C9C7D5DB
  ; word 0xBAB4A6A8828C9E90CAC4D6D8F2FCEEE0
  ; word 0x5A544648626C7E702A243638121C0E00 ]`;;

let joined_FFmul_0E = new_definition `joined_FFmul_0E:2048 word =
  word_join_list_16_128 FFmul_0E`;;


(* ========================================================================= *)
(* AES Intrinsics                                                            *)
(* ========================================================================= *)

let aes_sub_byte = new_definition
`aes_sub_byte (GF: 2048 word) (pos:8 word) : 8 word =
  (word_subword:2048 word->(num#num)->8 word) GF ((val pos)*8, 8)`;;

let aes_sub_bytes_select = new_definition
`aes_sub_bytes_select (GF:2048 word) (op:128 word) (i : num) : 8 word =
  let pos = (word_subword:128 word->(num#num)->8 word) op (i*8, 8) in
  aes_sub_byte GF pos`;;

(* Parameterize out GF2 so that it works both for
   aes_sub_bytes and aes_inv_sub_bytes *)
let aes_sub_bytes = new_definition
`aes_sub_bytes (GF:2048 word) (op:(128)word) : (128)word =
  (word_join_list_16_8
    [ (aes_sub_bytes_select GF op 15)
    ; (aes_sub_bytes_select GF op 14)
    ; (aes_sub_bytes_select GF op 13)
    ; (aes_sub_bytes_select GF op 12)
    ; (aes_sub_bytes_select GF op 11)
    ; (aes_sub_bytes_select GF op 10)
    ; (aes_sub_bytes_select GF op 9)
    ; (aes_sub_bytes_select GF op 8)
    ; (aes_sub_bytes_select GF op 7)
    ; (aes_sub_bytes_select GF op 6)
    ; (aes_sub_bytes_select GF op 5)
    ; (aes_sub_bytes_select GF op 4)
    ; (aes_sub_bytes_select GF op 3)
    ; (aes_sub_bytes_select GF op 2)
    ; (aes_sub_bytes_select GF op 1)
    ; (aes_sub_bytes_select GF op 0)])`;;

let aes_shift_rows = new_definition `aes_shift_rows (op:(128)word) : (128)word =
  (word_join_list_16_8
    [ (word_subword op (88, 8))
    ; (word_subword op (48, 8))
    ; (word_subword op (8, 8))
    ; (word_subword op (96, 8))
    ; (word_subword op (56, 8))
    ; (word_subword op (16, 8))
    ; (word_subword op (104, 8))
    ; (word_subword op (64, 8))
    ; (word_subword op (24, 8))
    ; (word_subword op (112, 8))
    ; (word_subword op (72, 8))
    ; (word_subword op (32, 8))
    ; (word_subword op (120, 8))
    ; (word_subword op (80, 8))
    ; (word_subword op (40, 8))
    ; (word_subword op (0, 8))] )`;;

let aes_inv_shift_rows = new_definition `aes_inv_shift_rows (op:(128)word) : (128)word =
  word_join_list_16_8
  [ (word_subword op (24, 8))
  ; (word_subword op (48, 8))
  ; (word_subword op (72, 8))
  ; (word_subword op (96, 8))
  ; (word_subword op (120, 8))
  ; (word_subword op (16, 8))
  ; (word_subword op (40, 8))
  ; (word_subword op (64, 8))
  ; (word_subword op (88, 8))
  ; (word_subword op (112, 8))
  ; (word_subword op (8, 8))
  ; (word_subword op (32, 8))
  ; (word_subword op (56, 8))
  ; (word_subword op (80, 8))
  ; (word_subword op (104, 8))
  ; (word_subword op (0, 8)) ]`;;

let FFmul = new_definition `FFmul (joined_tb : 2048 word) (b : 8 word) : 8 word =
  (word_subword:2048 word->(num#num)->8 word) joined_tb ((val b)*8, 8) `;;
let FFmul02 = new_definition `FFmul02 : (8 word)->(8 word) = FFmul joined_FFmul_02`;;
let FFmul03 = new_definition `FFmul03 : (8 word)->(8 word) = FFmul joined_FFmul_03`;;
let FFmul09 = new_definition `FFmul09 : (8 word)->(8 word) = FFmul joined_FFmul_09`;;
let FFmul0B = new_definition `FFmul0B : (8 word)->(8 word) = FFmul joined_FFmul_0B`;;
let FFmul0D = new_definition `FFmul0D : (8 word)->(8 word) = FFmul joined_FFmul_0D`;;
let FFmul0E = new_definition `FFmul0E : (8 word)->(8 word) = FFmul joined_FFmul_0E`;;

let aes_mix_word = new_definition
`aes_mix_word (op:(128)word) (a:num) (b:num) (c:num) (d:num) : (8)word =
  word_xor (FFmul02 (word_subword op (a, 8)))
    (word_xor (FFmul03 (word_subword op (b, 8)))
      (word_xor (word_subword op (c, 8))
        (word_subword op (d, 8)))) `;;

let aes_mix_columns = new_definition `aes_mix_columns (op:(128)word) : (128)word =
    let out00 = aes_mix_word op 0 8 16 24 in
    let out10 = aes_mix_word op 8 16 24 0 in
    let out20 = aes_mix_word op 16 24 0 8 in
    let out30 = aes_mix_word op 24 0 8 16 in
    let out01 = aes_mix_word op 32 40 48 56 in
    let out11 = aes_mix_word op 40 48 56 32 in
    let out21 = aes_mix_word op 48 56 32 40 in
    let out31 = aes_mix_word op 56 32 40 48 in
    let out02 = aes_mix_word op 64 72 80 88 in
    let out12 = aes_mix_word op 72 80 88 64 in
    let out22 = aes_mix_word op 80 88 64 72 in
    let out32 = aes_mix_word op 88 64 72 80 in
    let out03 = aes_mix_word op 96 104 112 120 in
    let out13 = aes_mix_word op 104 112 120 96 in
    let out23 = aes_mix_word op 112 120 96 104 in
    let out33 = aes_mix_word op 120 96 104 112 in
    word_join_list_16_8
    [out33; out23; out13; out03; out32; out22; out12; out02;
     out31; out21; out11; out01; out30; out20; out10; out00] `;;

let aes_inv_mix_word = new_definition
  `aes_inv_mix_word (op:(128)word) (a:num) (b:num) (c:num) (d:num) : (8)word =
   word_xor (FFmul0E (word_subword op (a, 8)))
     (word_xor (FFmul0B (word_subword op (b, 8)))
       (word_xor (FFmul0D (word_subword op (c, 8)))
         (FFmul09 (word_subword op (d, 8))))) `;;

let aes_inv_mix_columns = new_definition `aes_inv_mix_columns (op:(128)word) : (128)word =
  let out00 = aes_inv_mix_word op 0 8 16 24 in
  let out10 = aes_inv_mix_word op 8 16 24 0 in
  let out20 = aes_inv_mix_word op 16 24 0 8 in
  let out30 = aes_inv_mix_word op 24 0 8 16 in
  let out01 = aes_inv_mix_word op 32 40 48 56 in
  let out11 = aes_inv_mix_word op 40 48 56 32 in
  let out21 = aes_inv_mix_word op 48 56 32 40 in
  let out31 = aes_inv_mix_word op 56 32 40 48 in
  let out02 = aes_inv_mix_word op 64 72 80 88 in
  let out12 = aes_inv_mix_word op 72 80 88 64 in
  let out22 = aes_inv_mix_word op 80 88 64 72 in
  let out32 = aes_inv_mix_word op 88 64 72 80 in
  let out03 = aes_inv_mix_word op 96 104 112 120 in
  let out13 = aes_inv_mix_word op 104 112 120 96 in
  let out23 = aes_inv_mix_word op 112 120 96 104 in
  let out33 = aes_inv_mix_word op 120 96 104 112 in
  word_join_list_16_8
  [out33; out23; out13; out03; out32; out22; out12; out02;
   out31; out21; out11; out01; out30; out20; out10; out00] `;;

let aes_rotword = new_definition `aes_rotword (op:(32)word) : (32)word =
  ((word_join:8 word->24 word->32 word) (word_subword op (0,8))
    ((word_join:8 word->16 word->24 word) (word_subword op (24,8))
      ((word_join:8 word->8 word->16 word) (word_subword op (16,8))
        (word_subword op (8,8)))))`;;

let aes_subword = new_definition `aes_subword (op:(32)word) : (32)word =
  ((word_join:8 word->24 word->32 word) (aes_sub_byte joined_GF2 (word_subword op (24,8)))
    ((word_join:8 word->16 word->24 word) (aes_sub_byte joined_GF2 (word_subword op (16,8)))
      ((word_join:8 word->8 word->16 word) (aes_sub_byte joined_GF2 (word_subword op (8,8)))
        (aes_sub_byte joined_GF2 (word_subword op (0,8))))))`;;

(************************************************)
(** CONVERSIONS                                **)
(************************************************)

(* EL_CONV is a conversion for converting EL calls.
   We note that the EL calls in this file are for calculating word_join
   from constant tables. This means that the result could be precomputed
   and stored as clauses before-hand. This greatly increase the conversion
   speed. The EL conversion code and idea is from John Harrison. *)
(* Precalculate the conversion of EL n xxx when the list is of 16x(128 word) *)
let EL_16_128_CLAUSES =
  let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15]:128 word` in
  map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--15);;
(* Precalculate the conversion of EL n xxx when the list is of 16x(8 word) *)
let EL_16_8_CLAUSES =
    let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15]:8 word` in
    map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--15);;

(* Conversions for word functions *)
let WORD_JOIN_LIST_CONV FN CLAUSES =
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [FN] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV CLAUSES THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let WORD_JOIN_LIST_16_128_CONV = WORD_JOIN_LIST_CONV word_join_list_16_128 EL_16_128_CLAUSES;;
let WORD_JOIN_LIST_16_8_CONV = WORD_JOIN_LIST_CONV word_join_list_16_8 EL_16_8_CLAUSES;;

let JOINED_CONV joined_FN FN =
  GEN_REWRITE_CONV I [joined_FN] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [FN] THENC
  WORD_JOIN_LIST_16_128_CONV THENC
  DEPTH_CONV WORD_JOIN_CONV;;

(* Precompute joined_GF2 clause for speed *)
let JOINED_GF2_CLAUSE = (JOINED_CONV joined_GF2 GF2) `joined_GF2`;;
(* Precompute joined_GF2_inv clause for speed *)
let JOINED_GF2_INV_CLAUSE = (JOINED_CONV joined_GF2_inv GF2_inv) `joined_GF2_inv`;;
(* Precompute joined_FFmul_02 clause for speed *)
let JOINED_FFMUL_02_CLAUSE = (JOINED_CONV joined_FFmul_02 FFmul_02) `joined_FFmul_02`;;
(* Precompute joined_FFmul_03 clause for speed *)
let JOINED_FFMUL_03_CLAUSE = (JOINED_CONV joined_FFmul_03 FFmul_03) `joined_FFmul_03`;;
(* Precompute joined_FFmul_0E clause for speed *)
let JOINED_FFMUL_0E_CLAUSE = (JOINED_CONV joined_FFmul_0E FFmul_0E) `joined_FFmul_0E`;;
(* Precompute joined_FFmul_0B clause for speed *)
let JOINED_FFMUL_0B_CLAUSE = (JOINED_CONV joined_FFmul_0B FFmul_0B) `joined_FFmul_0B`;;
(* Precompute joined_FFmul_0D clause for speed *)
let JOINED_FFMUL_0D_CLAUSE = (JOINED_CONV joined_FFmul_0D FFmul_0D) `joined_FFmul_0D`;;
(* Precompute joined_FFmul_09 clause for speed *)
let JOINED_FFMUL_09_CLAUSE = (JOINED_CONV joined_FFmul_09 FFmul_09) `joined_FFmul_09`;;

let AES_SUB_BYTE_CONV =
  REWRITE_CONV [aes_sub_byte] THENC
  (GEN_REWRITE_CONV ONCE_DEPTH_CONV [JOINED_GF2_CLAUSE; JOINED_GF2_INV_CLAUSE]) THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AES_SUB_BYTES_SELECT_CONV =
  REWRITE_CONV [aes_sub_bytes_select] THENC
  AES_SUB_BYTE_CONV THENC
  TOP_DEPTH_CONV let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AES_SUB_BYTES_CONV =
  REWRITE_CONV [aes_sub_bytes] THENC
  AES_SUB_BYTES_SELECT_CONV THENC
  WORD_JOIN_LIST_16_8_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AES_SHIFT_ROWS_COMMON_CONV FN =
  REWRITE_CONV [FN] THENC
  WORD_JOIN_LIST_16_8_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AES_SHIFT_ROWS_CONV =
  AES_SHIFT_ROWS_COMMON_CONV aes_shift_rows;;
let AES_INV_SHIFT_ROWS_CONV =
  AES_SHIFT_ROWS_COMMON_CONV aes_inv_shift_rows;;

let FFMUL_CONV FN CL =
  REWRITE_CONV [FN; FFmul] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [CL] THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let FFMUL02_CONV =
  FFMUL_CONV FFmul02 JOINED_FFMUL_02_CLAUSE;;
let FFMUL03_CONV =
  FFMUL_CONV FFmul03 JOINED_FFMUL_03_CLAUSE;;
let FFMUL0E_CONV =
  FFMUL_CONV FFmul0E JOINED_FFMUL_0E_CLAUSE;;
let FFMUL0B_CONV =
  FFMUL_CONV FFmul0B JOINED_FFMUL_0B_CLAUSE;;
let FFMUL0D_CONV =
  FFMUL_CONV FFmul0D JOINED_FFMUL_0D_CLAUSE;;
let FFMUL09_CONV =
  FFMUL_CONV FFmul09 JOINED_FFMUL_09_CLAUSE;;

let AES_MIX_WORD_CONV =
  REWRITE_CONV [aes_mix_word] THENC
  FFMUL02_CONV THENC
  FFMUL03_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AES_MIX_COLUMNS_CONV =
  REWRITE_CONV [aes_mix_columns] THENC
  AES_MIX_WORD_CONV THENC
  WORD_JOIN_LIST_16_8_CONV THENC
  TOP_DEPTH_CONV let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AES_INV_MIX_WORD_CONV =
  REWRITE_CONV [aes_inv_mix_word] THENC
  FFMUL0E_CONV THENC
  FFMUL0B_CONV THENC
  FFMUL0D_CONV THENC
  FFMUL09_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AES_INV_MIX_COLUMNS_CONV =
  REWRITE_CONV [aes_inv_mix_columns] THENC
  AES_INV_MIX_WORD_CONV THENC
  WORD_JOIN_LIST_16_8_CONV THENC
  TOP_DEPTH_CONV let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AES_ROTWORD_CONV =
  REWRITE_CONV [aes_rotword] THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AES_SUBWORD_CONV =
  REWRITE_CONV [aes_subword] THENC
  AES_SUB_BYTE_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
