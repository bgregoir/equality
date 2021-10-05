Require Import Eqdep_dec.

From mathcomp Require Import all_ssreflect.
Require Import core_defs  tag.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import PArith.
Open Scope positive_scope.

Inductive t := 
| T1
| T2
| T3
| T4
| T5
| T6
| T7
| T8
| T9
| T10
| T11
| T12
| T13
| T14
| T15
| T16
| T17
| T18
| T19
| T20
| T21
| T22
| T23
| T24
| T25
| T26
| T27
| T28
| T29
| T30
| T31
| T32
| T33
| T34
| T35
| T36
| T37
| T38
| T39
| T40
| T41
| T42
| T43
| T44
| T45
| T46
| T47
| T48
| T49
| T50
| T51
| T52
| T53
| T54
| T55
| T56
| T57
| T58
| T59
| T60
| T61
| T62
| T63
| T64
| T65
| T66
| T67
| T68
| T69
| T70
| T71
| T72
| T73
| T74
| T75
| T76
| T77
| T78
| T79
| T80
| T81
| T82
| T83
| T84
| T85
| T86
| T87
| T88
| T89
| T90
| T91
| T92
| T93
| T94
| T95
| T96
| T97
| T98
| T99
| T100
| T101
| T102
| T103
| T104
| T105
| T106
| T107
| T108
| T109
| T110
| T111
| T112
| T113
| T114
| T115
| T116
| T117
| T118
| T119
| T120
| T121
| T122
| T123
| T124
| T125
| T126
| T127
| T128
| T129
| T130
| T131
| T132
| T133
| T134
| T135
| T136
| T137
| T138
| T139
| T140
| T141
| T142
| T143
| T144
| T145
| T146
| T147
| T148
| T149
| T150
| T151
| T152
| T153
| T154
| T155
| T156
| T157
| T158
| T159
| T160
| T161
| T162
| T163
| T164
| T165
| T166
| T167
| T168
| T169
| T170
| T171
| T172
| T173
| T174
| T175
| T176
| T177
| T178
| T179
| T180
| T181
| T182
| T183
| T184
| T185
| T186
| T187
| T188
| T189
| T190
| T191
| T192
| T193
| T194
| T195
| T196
| T197
| T198
| T199.

Module AUX.

Elpi tag t.
Definition tag := t_tag. (* (x : t) :=
  match x with
  | T1   => 1  
  | T2   => 2  
  | T3   => 3  
  | T4   => 4  
  | T5   => 5  
  | T6   => 6  
  | T7   => 7  
  | T8   => 8  
  | T9   => 9  
  | T10  => 10 
  | T11  => 11 
  | T12  => 12 
  | T13  => 13 
  | T14  => 14 
  | T15  => 15 
  | T16  => 16 
  | T17  => 17 
  | T18  => 18 
  | T19  => 19 
  | T20  => 20 
  | T21  => 21 
  | T22  => 22 
  | T23  => 23 
  | T24  => 24 
  | T25  => 25 
  | T26  => 26 
  | T27  => 27 
  | T28  => 28 
  | T29  => 29 
  | T30  => 30 
  | T31  => 31 
  | T32  => 32 
  | T33  => 33 
  | T34  => 34 
  | T35  => 35 
  | T36  => 36 
  | T37  => 37 
  | T38  => 38 
  | T39  => 39 
  | T40  => 40 
  | T41  => 41 
  | T42  => 42 
  | T43  => 43 
  | T44  => 44 
  | T45  => 45 
  | T46  => 46 
  | T47  => 47 
  | T48  => 48 
  | T49  => 49 
  | T50  => 50 
  | T51  => 51 
  | T52  => 52 
  | T53  => 53 
  | T54  => 54 
  | T55  => 55 
  | T56  => 56 
  | T57  => 57 
  | T58  => 58 
  | T59  => 59 
  | T60  => 60 
  | T61  => 61 
  | T62  => 62 
  | T63  => 63 
  | T64  => 64 
  | T65  => 65 
  | T66  => 66 
  | T67  => 67 
  | T68  => 68 
  | T69  => 69 
  | T70  => 70 
  | T71  => 71 
  | T72  => 72 
  | T73  => 73 
  | T74  => 74 
  | T75  => 75 
  | T76  => 76 
  | T77  => 77 
  | T78  => 78 
  | T79  => 79 
  | T80  => 80 
  | T81  => 81 
  | T82  => 82 
  | T83  => 83 
  | T84  => 84 
  | T85  => 85 
  | T86  => 86 
  | T87  => 87 
  | T88  => 88 
  | T89  => 89 
  | T90  => 90 
  | T91  => 91 
  | T92  => 92 
  | T93  => 93 
  | T94  => 94 
  | T95  => 95 
  | T96  => 96 
  | T97  => 97 
  | T98  => 98 
  | T99  => 99 
  | T100 => 100
  | T101 => 101
  | T102 => 102
  | T103 => 103
  | T104 => 104
  | T105 => 105
  | T106 => 106
  | T107 => 107
  | T108 => 108
  | T109 => 109
  | T110 => 110
  | T111 => 111
  | T112 => 112
  | T113 => 113
  | T114 => 114
  | T115 => 115
  | T116 => 116
  | T117 => 117
  | T118 => 118
  | T119 => 119
  | T120 => 120
  | T121 => 121
  | T122 => 122
  | T123 => 123
  | T124 => 124
  | T125 => 125
  | T126 => 126
  | T127 => 127
  | T128 => 128
  | T129 => 129
  | T130 => 130
  | T131 => 131
  | T132 => 132
  | T133 => 133
  | T134 => 134
  | T135 => 135
  | T136 => 136
  | T137 => 137
  | T138 => 138
  | T139 => 139
  | T140 => 140
  | T141 => 141
  | T142 => 142
  | T143 => 143
  | T144 => 144
  | T145 => 145
  | T146 => 146
  | T147 => 147
  | T148 => 148
  | T149 => 149
  | T150 => 150
  | T151 => 151
  | T152 => 152
  | T153 => 153
  | T154 => 154
  | T155 => 155
  | T156 => 156
  | T157 => 157
  | T158 => 158
  | T159 => 159
  | T160 => 160
  | T161 => 161
  | T162 => 162
  | T163 => 163
  | T164 => 164
  | T165 => 165
  | T166 => 166
  | T167 => 167
  | T168 => 168
  | T169 => 169
  | T170 => 170
  | T171 => 171
  | T172 => 172
  | T173 => 173
  | T174 => 174
  | T175 => 175
  | T176 => 176
  | T177 => 177
  | T178 => 178
  | T179 => 179
  | T180 => 180
  | T181 => 181
  | T182 => 182
  | T183 => 183
  | T184 => 184
  | T185 => 185
  | T186 => 186
  | T187 => 187
  | T188 => 188
  | T189 => 189
  | T190 => 190
  | T191 => 191
  | T192 => 192
  | T193 => 193
  | T194 => 194
  | T195 => 195
  | T196 => 196
  | T197 => 197
  | T198 => 198
  | T199 => 199
  end.
*)

Definition fields_t (p:positive) : Type := unit.

Definition fields (x:t) : fields_t (tag x) := tt.

Definition construct (p:positive) : fields_t p -> option t := 
  match p with
  | 1   => fun _ => Some T1  
  | 2   => fun _ => Some T2  
  | 3   => fun _ => Some T3  
  | 4   => fun _ => Some T4  
  | 5   => fun _ => Some T5  
  | 6   => fun _ => Some T6  
  | 7   => fun _ => Some T7  
  | 8   => fun _ => Some T8  
  | 9   => fun _ => Some T9  
  | 10  => fun _ => Some T10 
  | 11  => fun _ => Some T11 
  | 12  => fun _ => Some T12 
  | 13  => fun _ => Some T13 
  | 14  => fun _ => Some T14 
  | 15  => fun _ => Some T15 
  | 16  => fun _ => Some T16 
  | 17  => fun _ => Some T17 
  | 18  => fun _ => Some T18 
  | 19  => fun _ => Some T19 
  | 20  => fun _ => Some T20 
  | 21  => fun _ => Some T21 
  | 22  => fun _ => Some T22 
  | 23  => fun _ => Some T23 
  | 24  => fun _ => Some T24 
  | 25  => fun _ => Some T25 
  | 26  => fun _ => Some T26 
  | 27  => fun _ => Some T27 
  | 28  => fun _ => Some T28 
  | 29  => fun _ => Some T29 
  | 30  => fun _ => Some T30 
  | 31  => fun _ => Some T31 
  | 32  => fun _ => Some T32 
  | 33  => fun _ => Some T33 
  | 34  => fun _ => Some T34 
  | 35  => fun _ => Some T35 
  | 36  => fun _ => Some T36 
  | 37  => fun _ => Some T37 
  | 38  => fun _ => Some T38 
  | 39  => fun _ => Some T39 
  | 40  => fun _ => Some T40 
  | 41  => fun _ => Some T41 
  | 42  => fun _ => Some T42 
  | 43  => fun _ => Some T43 
  | 44  => fun _ => Some T44 
  | 45  => fun _ => Some T45 
  | 46  => fun _ => Some T46 
  | 47  => fun _ => Some T47 
  | 48  => fun _ => Some T48 
  | 49  => fun _ => Some T49 
  | 50  => fun _ => Some T50 
  | 51  => fun _ => Some T51 
  | 52  => fun _ => Some T52 
  | 53  => fun _ => Some T53 
  | 54  => fun _ => Some T54 
  | 55  => fun _ => Some T55 
  | 56  => fun _ => Some T56 
  | 57  => fun _ => Some T57 
  | 58  => fun _ => Some T58 
  | 59  => fun _ => Some T59 
  | 60  => fun _ => Some T60 
  | 61  => fun _ => Some T61 
  | 62  => fun _ => Some T62 
  | 63  => fun _ => Some T63 
  | 64  => fun _ => Some T64 
  | 65  => fun _ => Some T65 
  | 66  => fun _ => Some T66 
  | 67  => fun _ => Some T67 
  | 68  => fun _ => Some T68 
  | 69  => fun _ => Some T69 
  | 70  => fun _ => Some T70 
  | 71  => fun _ => Some T71 
  | 72  => fun _ => Some T72 
  | 73  => fun _ => Some T73 
  | 74  => fun _ => Some T74 
  | 75  => fun _ => Some T75 
  | 76  => fun _ => Some T76 
  | 77  => fun _ => Some T77 
  | 78  => fun _ => Some T78 
  | 79  => fun _ => Some T79 
  | 80  => fun _ => Some T80 
  | 81  => fun _ => Some T81 
  | 82  => fun _ => Some T82 
  | 83  => fun _ => Some T83 
  | 84  => fun _ => Some T84 
  | 85  => fun _ => Some T85 
  | 86  => fun _ => Some T86 
  | 87  => fun _ => Some T87 
  | 88  => fun _ => Some T88 
  | 89  => fun _ => Some T89 
  | 90  => fun _ => Some T90 
  | 91  => fun _ => Some T91 
  | 92  => fun _ => Some T92 
  | 93  => fun _ => Some T93 
  | 94  => fun _ => Some T94 
  | 95  => fun _ => Some T95 
  | 96  => fun _ => Some T96 
  | 97  => fun _ => Some T97 
  | 98  => fun _ => Some T98 
  | 99  => fun _ => Some T99 
  | 100 => fun _ => Some T100
  | 101 => fun _ => Some T101
  | 102 => fun _ => Some T102
  | 103 => fun _ => Some T103
  | 104 => fun _ => Some T104
  | 105 => fun _ => Some T105
  | 106 => fun _ => Some T106
  | 107 => fun _ => Some T107
  | 108 => fun _ => Some T108
  | 109 => fun _ => Some T109
  | 110 => fun _ => Some T110
  | 111 => fun _ => Some T111
  | 112 => fun _ => Some T112
  | 113 => fun _ => Some T113
  | 114 => fun _ => Some T114
  | 115 => fun _ => Some T115
  | 116 => fun _ => Some T116
  | 117 => fun _ => Some T117
  | 118 => fun _ => Some T118
  | 119 => fun _ => Some T119
  | 120 => fun _ => Some T120
  | 121 => fun _ => Some T121
  | 122 => fun _ => Some T122
  | 123 => fun _ => Some T123
  | 124 => fun _ => Some T124
  | 125 => fun _ => Some T125
  | 126 => fun _ => Some T126
  | 127 => fun _ => Some T127
  | 128 => fun _ => Some T128
  | 129 => fun _ => Some T129
  | 130 => fun _ => Some T130
  | 131 => fun _ => Some T131
  | 132 => fun _ => Some T132
  | 133 => fun _ => Some T133
  | 134 => fun _ => Some T134
  | 135 => fun _ => Some T135
  | 136 => fun _ => Some T136
  | 137 => fun _ => Some T137
  | 138 => fun _ => Some T138
  | 139 => fun _ => Some T139
  | 140 => fun _ => Some T140
  | 141 => fun _ => Some T141
  | 142 => fun _ => Some T142
  | 143 => fun _ => Some T143
  | 144 => fun _ => Some T144
  | 145 => fun _ => Some T145
  | 146 => fun _ => Some T146
  | 147 => fun _ => Some T147
  | 148 => fun _ => Some T148
  | 149 => fun _ => Some T149
  | 150 => fun _ => Some T150
  | 151 => fun _ => Some T151
  | 152 => fun _ => Some T152
  | 153 => fun _ => Some T153
  | 154 => fun _ => Some T154
  | 155 => fun _ => Some T155
  | 156 => fun _ => Some T156
  | 157 => fun _ => Some T157
  | 158 => fun _ => Some T158
  | 159 => fun _ => Some T159
  | 160 => fun _ => Some T160
  | 161 => fun _ => Some T161
  | 162 => fun _ => Some T162
  | 163 => fun _ => Some T163
  | 164 => fun _ => Some T164
  | 165 => fun _ => Some T165
  | 166 => fun _ => Some T166
  | 167 => fun _ => Some T167
  | 168 => fun _ => Some T168
  | 169 => fun _ => Some T169
  | 170 => fun _ => Some T170
  | 171 => fun _ => Some T171
  | 172 => fun _ => Some T172
  | 173 => fun _ => Some T173
  | 174 => fun _ => Some T174
  | 175 => fun _ => Some T175
  | 176 => fun _ => Some T176
  | 177 => fun _ => Some T177
  | 178 => fun _ => Some T178
  | 179 => fun _ => Some T179
  | 180 => fun _ => Some T180
  | 181 => fun _ => Some T181
  | 182 => fun _ => Some T182
  | 183 => fun _ => Some T183
  | 184 => fun _ => Some T184
  | 185 => fun _ => Some T185
  | 186 => fun _ => Some T186
  | 187 => fun _ => Some T187
  | 188 => fun _ => Some T188
  | 189 => fun _ => Some T189
  | 190 => fun _ => Some T190
  | 191 => fun _ => Some T191
  | 192 => fun _ => Some T192
  | 193 => fun _ => Some T193
  | 194 => fun _ => Some T194
  | 195 => fun _ => Some T195
  | 196 => fun _ => Some T196
  | 197 => fun _ => Some T197
  | 198 => fun _ => Some T198
  | 199 => fun _ => Some T199
  | _   => fun _ => None
  end.

Lemma constructP x : construct (fields x) = Some x.
Proof. by case: x. Qed.

End AUX.

Local Instance t_obj : @obj t := 
  {| tag        := AUX.tag
   ; fields_t   := AUX.fields_t
   ; fields     := AUX.fields
   ; construct  := AUX.construct
   ; constructP := AUX.constructP |}.

Definition eqb_fields (t:positive) : fields_t t -> fields_t t -> bool := 
  eq_op.

(* Remark this is unusefull for this kind of type.
   This pattern is usefull only for recursive type or for polymorphic type (this allows to use the definition for nested inductive *)
Definition eqb (x1 x2:t) := 
  match x1 with
  | T1   => eqb_body eqb_fields (t1:=1  ) tt x2   
  | T2   => eqb_body eqb_fields (t1:=2  ) tt x2
  | T3   => eqb_body eqb_fields (t1:=3  ) tt x2
  | T4   => eqb_body eqb_fields (t1:=4  ) tt x2
  | T5   => eqb_body eqb_fields (t1:=5  ) tt x2
  | T6   => eqb_body eqb_fields (t1:=6  ) tt x2
  | T7   => eqb_body eqb_fields (t1:=7  ) tt x2
  | T8   => eqb_body eqb_fields (t1:=8  ) tt x2
  | T9   => eqb_body eqb_fields (t1:=9  ) tt x2
  | T10  => eqb_body eqb_fields (t1:=10 ) tt x2
  | T11  => eqb_body eqb_fields (t1:=11 ) tt x2
  | T12  => eqb_body eqb_fields (t1:=12 ) tt x2
  | T13  => eqb_body eqb_fields (t1:=13 ) tt x2
  | T14  => eqb_body eqb_fields (t1:=14 ) tt x2
  | T15  => eqb_body eqb_fields (t1:=15 ) tt x2
  | T16  => eqb_body eqb_fields (t1:=16 ) tt x2
  | T17  => eqb_body eqb_fields (t1:=17 ) tt x2
  | T18  => eqb_body eqb_fields (t1:=18 ) tt x2
  | T19  => eqb_body eqb_fields (t1:=19 ) tt x2
  | T20  => eqb_body eqb_fields (t1:=20 ) tt x2
  | T21  => eqb_body eqb_fields (t1:=21 ) tt x2
  | T22  => eqb_body eqb_fields (t1:=22 ) tt x2
  | T23  => eqb_body eqb_fields (t1:=23 ) tt x2
  | T24  => eqb_body eqb_fields (t1:=24 ) tt x2
  | T25  => eqb_body eqb_fields (t1:=25 ) tt x2
  | T26  => eqb_body eqb_fields (t1:=26 ) tt x2
  | T27  => eqb_body eqb_fields (t1:=27 ) tt x2
  | T28  => eqb_body eqb_fields (t1:=28 ) tt x2
  | T29  => eqb_body eqb_fields (t1:=29 ) tt x2
  | T30  => eqb_body eqb_fields (t1:=30 ) tt x2
  | T31  => eqb_body eqb_fields (t1:=31 ) tt x2
  | T32  => eqb_body eqb_fields (t1:=32 ) tt x2
  | T33  => eqb_body eqb_fields (t1:=33 ) tt x2
  | T34  => eqb_body eqb_fields (t1:=34 ) tt x2
  | T35  => eqb_body eqb_fields (t1:=35 ) tt x2
  | T36  => eqb_body eqb_fields (t1:=36 ) tt x2
  | T37  => eqb_body eqb_fields (t1:=37 ) tt x2
  | T38  => eqb_body eqb_fields (t1:=38 ) tt x2
  | T39  => eqb_body eqb_fields (t1:=39 ) tt x2
  | T40  => eqb_body eqb_fields (t1:=40 ) tt x2
  | T41  => eqb_body eqb_fields (t1:=41 ) tt x2
  | T42  => eqb_body eqb_fields (t1:=42 ) tt x2
  | T43  => eqb_body eqb_fields (t1:=43 ) tt x2
  | T44  => eqb_body eqb_fields (t1:=44 ) tt x2
  | T45  => eqb_body eqb_fields (t1:=45 ) tt x2
  | T46  => eqb_body eqb_fields (t1:=46 ) tt x2
  | T47  => eqb_body eqb_fields (t1:=47 ) tt x2
  | T48  => eqb_body eqb_fields (t1:=48 ) tt x2
  | T49  => eqb_body eqb_fields (t1:=49 ) tt x2
  | T50  => eqb_body eqb_fields (t1:=50 ) tt x2
  | T51  => eqb_body eqb_fields (t1:=51 ) tt x2
  | T52  => eqb_body eqb_fields (t1:=52 ) tt x2
  | T53  => eqb_body eqb_fields (t1:=53 ) tt x2
  | T54  => eqb_body eqb_fields (t1:=54 ) tt x2
  | T55  => eqb_body eqb_fields (t1:=55 ) tt x2
  | T56  => eqb_body eqb_fields (t1:=56 ) tt x2
  | T57  => eqb_body eqb_fields (t1:=57 ) tt x2
  | T58  => eqb_body eqb_fields (t1:=58 ) tt x2
  | T59  => eqb_body eqb_fields (t1:=59 ) tt x2
  | T60  => eqb_body eqb_fields (t1:=60 ) tt x2
  | T61  => eqb_body eqb_fields (t1:=61 ) tt x2
  | T62  => eqb_body eqb_fields (t1:=62 ) tt x2
  | T63  => eqb_body eqb_fields (t1:=63 ) tt x2
  | T64  => eqb_body eqb_fields (t1:=64 ) tt x2
  | T65  => eqb_body eqb_fields (t1:=65 ) tt x2
  | T66  => eqb_body eqb_fields (t1:=66 ) tt x2
  | T67  => eqb_body eqb_fields (t1:=67 ) tt x2
  | T68  => eqb_body eqb_fields (t1:=68 ) tt x2
  | T69  => eqb_body eqb_fields (t1:=69 ) tt x2
  | T70  => eqb_body eqb_fields (t1:=70 ) tt x2
  | T71  => eqb_body eqb_fields (t1:=71 ) tt x2
  | T72  => eqb_body eqb_fields (t1:=72 ) tt x2
  | T73  => eqb_body eqb_fields (t1:=73 ) tt x2
  | T74  => eqb_body eqb_fields (t1:=74 ) tt x2
  | T75  => eqb_body eqb_fields (t1:=75 ) tt x2
  | T76  => eqb_body eqb_fields (t1:=76 ) tt x2
  | T77  => eqb_body eqb_fields (t1:=77 ) tt x2
  | T78  => eqb_body eqb_fields (t1:=78 ) tt x2
  | T79  => eqb_body eqb_fields (t1:=79 ) tt x2
  | T80  => eqb_body eqb_fields (t1:=80 ) tt x2
  | T81  => eqb_body eqb_fields (t1:=81 ) tt x2
  | T82  => eqb_body eqb_fields (t1:=82 ) tt x2
  | T83  => eqb_body eqb_fields (t1:=83 ) tt x2
  | T84  => eqb_body eqb_fields (t1:=84 ) tt x2
  | T85  => eqb_body eqb_fields (t1:=85 ) tt x2
  | T86  => eqb_body eqb_fields (t1:=86 ) tt x2
  | T87  => eqb_body eqb_fields (t1:=87 ) tt x2
  | T88  => eqb_body eqb_fields (t1:=88 ) tt x2
  | T89  => eqb_body eqb_fields (t1:=89 ) tt x2
  | T90  => eqb_body eqb_fields (t1:=90 ) tt x2
  | T91  => eqb_body eqb_fields (t1:=91 ) tt x2
  | T92  => eqb_body eqb_fields (t1:=92 ) tt x2
  | T93  => eqb_body eqb_fields (t1:=93 ) tt x2
  | T94  => eqb_body eqb_fields (t1:=94 ) tt x2
  | T95  => eqb_body eqb_fields (t1:=95 ) tt x2
  | T96  => eqb_body eqb_fields (t1:=96 ) tt x2
  | T97  => eqb_body eqb_fields (t1:=97 ) tt x2
  | T98  => eqb_body eqb_fields (t1:=98 ) tt x2
  | T99  => eqb_body eqb_fields (t1:=99 ) tt x2
  | T100 => eqb_body eqb_fields (t1:=100) tt x2
  | T101 => eqb_body eqb_fields (t1:=101) tt x2
  | T102 => eqb_body eqb_fields (t1:=102) tt x2
  | T103 => eqb_body eqb_fields (t1:=103) tt x2
  | T104 => eqb_body eqb_fields (t1:=104) tt x2
  | T105 => eqb_body eqb_fields (t1:=105) tt x2
  | T106 => eqb_body eqb_fields (t1:=106) tt x2
  | T107 => eqb_body eqb_fields (t1:=107) tt x2
  | T108 => eqb_body eqb_fields (t1:=108) tt x2
  | T109 => eqb_body eqb_fields (t1:=109) tt x2
  | T110 => eqb_body eqb_fields (t1:=110) tt x2
  | T111 => eqb_body eqb_fields (t1:=111) tt x2
  | T112 => eqb_body eqb_fields (t1:=112) tt x2
  | T113 => eqb_body eqb_fields (t1:=113) tt x2
  | T114 => eqb_body eqb_fields (t1:=114) tt x2
  | T115 => eqb_body eqb_fields (t1:=115) tt x2
  | T116 => eqb_body eqb_fields (t1:=116) tt x2
  | T117 => eqb_body eqb_fields (t1:=117) tt x2
  | T118 => eqb_body eqb_fields (t1:=118) tt x2
  | T119 => eqb_body eqb_fields (t1:=119) tt x2
  | T120 => eqb_body eqb_fields (t1:=120) tt x2
  | T121 => eqb_body eqb_fields (t1:=121) tt x2
  | T122 => eqb_body eqb_fields (t1:=122) tt x2
  | T123 => eqb_body eqb_fields (t1:=123) tt x2
  | T124 => eqb_body eqb_fields (t1:=124) tt x2
  | T125 => eqb_body eqb_fields (t1:=125) tt x2
  | T126 => eqb_body eqb_fields (t1:=126) tt x2
  | T127 => eqb_body eqb_fields (t1:=127) tt x2
  | T128 => eqb_body eqb_fields (t1:=128) tt x2
  | T129 => eqb_body eqb_fields (t1:=129) tt x2
  | T130 => eqb_body eqb_fields (t1:=130) tt x2
  | T131 => eqb_body eqb_fields (t1:=131) tt x2
  | T132 => eqb_body eqb_fields (t1:=132) tt x2
  | T133 => eqb_body eqb_fields (t1:=133) tt x2
  | T134 => eqb_body eqb_fields (t1:=134) tt x2
  | T135 => eqb_body eqb_fields (t1:=135) tt x2
  | T136 => eqb_body eqb_fields (t1:=136) tt x2
  | T137 => eqb_body eqb_fields (t1:=137) tt x2
  | T138 => eqb_body eqb_fields (t1:=138) tt x2
  | T139 => eqb_body eqb_fields (t1:=139) tt x2
  | T140 => eqb_body eqb_fields (t1:=140) tt x2
  | T141 => eqb_body eqb_fields (t1:=141) tt x2
  | T142 => eqb_body eqb_fields (t1:=142) tt x2
  | T143 => eqb_body eqb_fields (t1:=143) tt x2
  | T144 => eqb_body eqb_fields (t1:=144) tt x2
  | T145 => eqb_body eqb_fields (t1:=145) tt x2
  | T146 => eqb_body eqb_fields (t1:=146) tt x2
  | T147 => eqb_body eqb_fields (t1:=147) tt x2
  | T148 => eqb_body eqb_fields (t1:=148) tt x2
  | T149 => eqb_body eqb_fields (t1:=149) tt x2
  | T150 => eqb_body eqb_fields (t1:=150) tt x2
  | T151 => eqb_body eqb_fields (t1:=151) tt x2
  | T152 => eqb_body eqb_fields (t1:=152) tt x2
  | T153 => eqb_body eqb_fields (t1:=153) tt x2
  | T154 => eqb_body eqb_fields (t1:=154) tt x2
  | T155 => eqb_body eqb_fields (t1:=155) tt x2
  | T156 => eqb_body eqb_fields (t1:=156) tt x2
  | T157 => eqb_body eqb_fields (t1:=157) tt x2
  | T158 => eqb_body eqb_fields (t1:=158) tt x2
  | T159 => eqb_body eqb_fields (t1:=159) tt x2
  | T160 => eqb_body eqb_fields (t1:=160) tt x2
  | T161 => eqb_body eqb_fields (t1:=161) tt x2
  | T162 => eqb_body eqb_fields (t1:=162) tt x2
  | T163 => eqb_body eqb_fields (t1:=163) tt x2
  | T164 => eqb_body eqb_fields (t1:=164) tt x2
  | T165 => eqb_body eqb_fields (t1:=165) tt x2
  | T166 => eqb_body eqb_fields (t1:=166) tt x2
  | T167 => eqb_body eqb_fields (t1:=167) tt x2
  | T168 => eqb_body eqb_fields (t1:=168) tt x2
  | T169 => eqb_body eqb_fields (t1:=169) tt x2
  | T170 => eqb_body eqb_fields (t1:=170) tt x2
  | T171 => eqb_body eqb_fields (t1:=171) tt x2
  | T172 => eqb_body eqb_fields (t1:=172) tt x2
  | T173 => eqb_body eqb_fields (t1:=173) tt x2
  | T174 => eqb_body eqb_fields (t1:=174) tt x2
  | T175 => eqb_body eqb_fields (t1:=175) tt x2
  | T176 => eqb_body eqb_fields (t1:=176) tt x2
  | T177 => eqb_body eqb_fields (t1:=177) tt x2
  | T178 => eqb_body eqb_fields (t1:=178) tt x2
  | T179 => eqb_body eqb_fields (t1:=179) tt x2
  | T180 => eqb_body eqb_fields (t1:=180) tt x2
  | T181 => eqb_body eqb_fields (t1:=181) tt x2
  | T182 => eqb_body eqb_fields (t1:=182) tt x2
  | T183 => eqb_body eqb_fields (t1:=183) tt x2
  | T184 => eqb_body eqb_fields (t1:=184) tt x2
  | T185 => eqb_body eqb_fields (t1:=185) tt x2
  | T186 => eqb_body eqb_fields (t1:=186) tt x2
  | T187 => eqb_body eqb_fields (t1:=187) tt x2
  | T188 => eqb_body eqb_fields (t1:=188) tt x2
  | T189 => eqb_body eqb_fields (t1:=189) tt x2
  | T190 => eqb_body eqb_fields (t1:=190) tt x2
  | T191 => eqb_body eqb_fields (t1:=191) tt x2
  | T192 => eqb_body eqb_fields (t1:=192) tt x2
  | T193 => eqb_body eqb_fields (t1:=193) tt x2
  | T194 => eqb_body eqb_fields (t1:=194) tt x2
  | T195 => eqb_body eqb_fields (t1:=195) tt x2
  | T196 => eqb_body eqb_fields (t1:=196) tt x2
  | T197 => eqb_body eqb_fields (t1:=197) tt x2
  | T198 => eqb_body eqb_fields (t1:=198) tt x2
  | T199 => eqb_body eqb_fields (t1:=199) tt x2
  end.

Lemma eqb_correct (x : t) : eqb_correct_on eqb x.
Proof.
  by case: x;
  rewrite /eqb_correct_on /eqb => ha htt;
  apply (@eqb_body_correct _ t_obj eqb_fields).
Qed.

Lemma eqb_refl (x:t) : eqb_refl_on eqb x.
Proof.
  by case: x; apply (@eqb_body_refl _ t_obj eqb_fields).
Qed.

Lemma eqbP (x1 x2 : t) : reflect (x1 = x2) (eqb x1 x2).
Proof. apply (iffP idP);[ apply eqb_correct | move=> ->; apply eqb_refl]. Qed.



