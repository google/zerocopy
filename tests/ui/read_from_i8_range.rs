// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use zerocopy::*;

#[derive(FromBytes)]
#[repr(i8)]
enum Foo {
    Variant0 = -128,
    Variant1 = -127,
    Variant2 = -126,
    Variant3 = -125,
    Variant4 = -124,
    Variant5 = -123,
    Variant6 = -122,
    Variant7 = -121,
    Variant8 = -120,
    Variant9 = -119,
    Variant10 = -118,
    Variant11 = -117,
    Variant12 = -116,
    Variant13 = -115,
    Variant14 = -114,
    Variant15 = -113,
    Variant16 = -112,
    Variant17 = -111,
    Variant18 = -110,
    Variant19 = -109,
    Variant20 = -108,
    Variant21 = -107,
    Variant22 = -106,
    Variant23 = -105,
    Variant24 = -104,
    Variant25 = -103,
    Variant26 = -102,
    Variant27 = -101,
    Variant28 = -100,
    Variant29 = -99,
    Variant30 = -98,
    Variant31 = -97,
    Variant32 = -96,
    Variant33 = -95,
    Variant34 = -94,
    Variant35 = -93,
    Variant36 = -92,
    Variant37 = -91,
    Variant38 = -90,
    Variant39 = -89,
    Variant40 = -88,
    Variant41 = -87,
    Variant42 = -86,
    Variant43 = -85,
    Variant44 = -84,
    Variant45 = -83,
    Variant46 = -82,
    Variant47 = -81,
    Variant48 = -80,
    Variant49 = -79,
    Variant50 = -78,
    Variant51 = -77,
    Variant52 = -76,
    Variant53 = -75,
    Variant54 = -74,
    Variant55 = -73,
    Variant56 = -72,
    Variant57 = -71,
    Variant58 = -70,
    Variant59 = -69,
    Variant60 = -68,
    Variant61 = -67,
    Variant62 = -66,
    Variant63 = -65,
    Variant64 = -64,
    Variant65 = -63,
    Variant66 = -62,
    Variant67 = -61,
    Variant68 = -60,
    Variant69 = -59,
    Variant70 = -58,
    Variant71 = -57,
    Variant72 = -56,
    Variant73 = -55,
    Variant74 = -54,
    Variant75 = -53,
    Variant76 = -52,
    Variant77 = -51,
    Variant78 = -50,
    Variant79 = -49,
    Variant80 = -48,
    Variant81 = -47,
    Variant82 = -46,
    Variant83 = -45,
    Variant84 = -44,
    Variant85 = -43,
    Variant86 = -42,
    Variant87 = -41,
    Variant88 = -40,
    Variant89 = -39,
    Variant90 = -38,
    Variant91 = -37,
    Variant92 = -36,
    Variant93 = -35,
    Variant94 = -34,
    Variant95 = -33,
    Variant96 = -32,
    Variant97 = -31,
    Variant98 = -30,
    Variant99 = -29,
    Variant100 = -28,
    Variant101 = -27,
    Variant102 = -26,
    Variant103 = -25,
    Variant104 = -24,
    Variant105 = -23,
    Variant106 = -22,
    Variant107 = -21,
    Variant108 = -20,
    Variant109 = -19,
    Variant110 = -18,
    Variant111 = -17,
    Variant112 = -16,
    Variant113 = -15,
    Variant114 = -14,
    Variant115 = -13,
    Variant116 = -12,
    Variant117 = -11,
    Variant118 = -10,
    Variant119 = -9,
    Variant120 = -8,
    Variant121 = -7,
    Variant122 = -6,
    Variant123 = -5,
    Variant124 = -4,
    Variant125 = -3,
    Variant126 = -2,
    Variant127 = -1,
    Variant128 = 0,
    Variant129 = 1,
    Variant130 = 2,
    Variant131 = 3,
    Variant132 = 4,
    Variant133 = 5,
    Variant134 = 6,
    Variant135 = 7,
    Variant136 = 8,
    Variant137 = 9,
    Variant138 = 10,
    Variant139 = 11,
    Variant140 = 12,
    Variant141 = 13,
    Variant142 = 14,
    Variant143 = 15,
    Variant144 = 16,
    Variant145 = 17,
    Variant146 = 18,
    Variant147 = 19,
    Variant148 = 20,
    Variant149 = 21,
    Variant150 = 22,
    Variant151 = 23,
    Variant152 = 24,
    Variant153 = 25,
    Variant154 = 26,
    Variant155 = 27,
    Variant156 = 28,
    Variant157 = 29,
    Variant158 = 30,
    Variant159 = 31,
    Variant160 = 32,
    Variant161 = 33,
    Variant162 = 34,
    Variant163 = 35,
    Variant164 = 36,
    Variant165 = 37,
    Variant166 = 38,
    Variant167 = 39,
    Variant168 = 40,
    Variant169 = 41,
    Variant170 = 42,
    Variant171 = 43,
    Variant172 = 44,
    Variant173 = 45,
    Variant174 = 46,
    Variant175 = 47,
    Variant176 = 48,
    Variant177 = 49,
    Variant178 = 50,
    Variant179 = 51,
    Variant180 = 52,
    Variant181 = 53,
    Variant182 = 54,
    Variant183 = 55,
    Variant184 = 56,
    Variant185 = 57,
    Variant186 = 58,
    Variant187 = 59,
    Variant188 = 60,
    Variant189 = 61,
    Variant190 = 62,
    Variant191 = 63,
    Variant192 = 64,
    Variant193 = 65,
    Variant194 = 66,
    Variant195 = 67,
    Variant196 = 68,
    Variant197 = 69,
    Variant198 = 70,
    Variant199 = 71,
    Variant200 = 72,
    Variant201 = 73,
    Variant202 = 74,
    Variant203 = 75,
    Variant204 = 76,
    Variant205 = 77,
    Variant206 = 78,
    Variant207 = 79,
    Variant208 = 80,
    Variant209 = 81,
    Variant210 = 82,
    Variant211 = 83,
    Variant212 = 84,
    Variant213 = 85,
    Variant214 = 86,
    Variant215 = 87,
    Variant216 = 88,
    Variant217 = 89,
    Variant218 = 90,
    Variant219 = 91,
    Variant220 = 92,
    Variant221 = 93,
    Variant222 = 94,
    Variant223 = 95,
    Variant224 = 96,
    Variant225 = 97,
    Variant226 = 98,
    Variant227 = 99,
    Variant228 = 100,
    Variant229 = 101,
    Variant230 = 102,
    Variant231 = 103,
    Variant232 = 104,
    Variant233 = 105,
    Variant234 = 106,
    Variant235 = 107,
    Variant236 = 108,
    Variant237 = 109,
    Variant238 = 110,
    Variant239 = 111,
    Variant240 = 112,
    Variant241 = 113,
    Variant242 = 114,
    Variant243 = 115,
    Variant244 = 116,
    Variant245 = 117,
    Variant246 = 118,
    Variant247 = 119,
    Variant248 = 120,
    Variant249 = 121,
    Variant250 = 122,
    Variant251 = 123,
    Variant252 = 124,
    Variant253 = 125,
    Variant254 = 126,
    Variant255 = 127,
}

fn main() {
    let _ = Foo::read_from([-1].as_slice()).unwrap();
}