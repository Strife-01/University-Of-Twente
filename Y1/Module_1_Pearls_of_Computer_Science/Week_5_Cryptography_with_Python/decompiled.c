
char* __convention("regparm") sub_0(int32_t arg1, char* arg2, char* arg3, int32_t arg4 @ ebp, int32_t* arg5 @ esi, void* arg6 @ edi, void arg7 @ x87control, long double arg8 @ st0, void* arg9, void* arg10)
{
    *arg5 ^= arg4;
    *0x3020370a = (RORD(*0x3020370a, arg3));
    *(arg6 + 0x62) &= *arg3[1];  {  // {"                \r\n16 0 obj\r<<…"}}
    int32_t var_4 = 0xd;
    int32_t eflags;
    int32_t eflags_1;
    char temp0;
    temp0 = __das(((arg1 & 0x2d464450) | 0xcfe3e225), eflags);
    int32_t eax;
    eax = temp0;
    char* fsbase;
    *(fsbase + arg3) &= *arg2[1];
    int32_t eflags_2;
    char temp0_1;
    temp0_1 = __das(eax, eflags_1);
    eax = temp0_1;
    *(arg2 + arg5) &= *arg2[1];
    *arg2 ^= *arg2[1];
    int32_t eflags_3;
    char temp0_2;
    temp0_2 = __aaa(eax, *eax[1], eflags_2);
    eax = temp0_2;
    char __return_addr_2;
    *eax[1] = __return_addr_2;
    int32_t eflags_4;
    char temp0_3;
    temp0_3 = __das(eax, eflags_3);
    eax = temp0_3;
    *arg3 &= *arg2[1];
    *(arg6 - 1) ^= *arg3[1];
    int32_t ebp_1 = ((*(arg5 + 0x65) * 0x7a697261) + 1);  {  // {"             \r\n16 0 obj\r<</De…"}}
    char* ebx;
    *ebx &= *arg2[1];
    int32_t eflags_5;
    char temp0_4;
    temp0_4 = __aaa(eax, *eax[1], eflags_4);
    eax = temp0_4;
    *eax[1] = __return_addr_2;
    *((arg6 - 1) + arg5);
    int32_t eflags_6;
    char temp0_5;
    temp0_5 = __das(eax, eflags_5);
    eax = temp0_5;
    *arg3 &= *arg2[1];
    int32_t eflags_7;
    char temp0_6;
    temp0_6 = __das(eax, eflags_6);
    eax = temp0_6;
    *(arg3 + (arg5 - 1)) &= *arg2[1];
    int32_t eflags_8;
    char temp0_7;
    temp0_7 = __aaa(eax, *eax[1], eflags_7);
    eax = temp0_7;
    *eax[1] = __return_addr_2;
    *arg2[1] ^= *((arg6 - 1) + ebp_1);
    ebx[0x20] &= ebx;  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
    int32_t eax_1;
    eax_1 = ((eax - 1) ^ 0x37);  {  // {"37847/N 1/T 41724/H [ 477 159]>>…"}}
    int32_t eflags_9;
    char temp0_8;
    temp0_8 = __aaa(eax_1, *eax_1[1], eflags_8);
    eax_1 = temp0_8;
    *eax_1[1] = __return_addr_2;
    *arg3 &= *arg2[1];
    char* eax_3 = ((eax_1 ^ 0x3e3e5d39) | 0x6f646e65);
    __bound_gprv_mema32(ebp_1, *(arg2 + 0xd));
    *eax_3 &= *eax_3[1];
    *eax_3 &= *eax_3[1];
    *eax_3 &= *eax_3[1];
    *eax_3 &= *eax_3[1];
    *eax_3 &= *eax_3[1];
    *eax_3 &= *eax_3[1];
    *eax_3 &= *eax_3[1];
    *eax_3 &= *eax_3[1];
    *eax_3 &= *eax_3[1];
    *0x2036310a &= arg3;
    *eax_3 ^= *eax_3[1];
    __outsd(arg2, *(arg5 - 1), (arg5 - 1), eflags_9);
    __bound_gprv_mema32(ebp_1, *(arg2 + 0xd));
    bool cond:0 = eax_3 < 0x3c;  {  // {"/N 1/T 41724/H [ 477 159]>>\rend…"}}
    bool cond:1 = eax_3 >= 0x3c;  {  // {"/N 1/T 41724/H [ 477 159]>>\rend…"}}
    int32_t eflags_10;
    char temp0_9;
    temp0_9 = __das(eax_3, eflags_9);
    eax_3 = temp0_9;
    int32_t eflags_11;
    uint16_t* gsbase;
    int16_t temp0_10;
    temp0_10 = __arpl_memw_gpr16(*(gsbase + (arg6 + 0x63)), ebp_1);  {  // {"               \r\n16 0 obj\r<</…"}}
    *(gsbase + (arg6 + 0x63)) = temp0_10;  {  // {"               \r\n16 0 obj\r<</…"}}
    char* edi_1 = eax_3;
    void var_6;
    void* esi_2 = &var_6;
    void* var_5;
    void* ebp_2 = var_5;
    void* const __return_addr_1 = __return_addr;
    void* edx = arg9;
    void* ecx = arg10;
    char* result = result_1;
    void* esp_1 = &arg_13;
    void* ebx_1;
    int16_t ss;
    
    if (!(cond:0))
    {
        if (!(cond:1))
        {
            __return_addr_2 = __return_addr_1;
            ebx_1 = (__return_addr_1 + 1);
            bool cond:9_1 = __return_addr_2 == 0xffffffff;
            esi_2 = __outsd(edx, *esi_2, esi_2, eflags_11);
            uint8_t temp0_11;
            temp0_11 = __insb(edi_1, edx, eflags_11);
            *edi_1 = temp0_11;
            
            if (__return_addr_2 != 0xffffffff)
            {
                *edx[1] ^= *esi_2;
                goto label_102;
            }
            
            esi_2 = __outsb(edx, *esi_2, esi_2, eflags_11);
            
            if (result < 0x2f)  {  // {"/O 10/E 37847/N 1/T 41724/H [ 47…"}}
            {
                result ^= 0x2f;  {  // {"/O 10/E 37847/N 1/T 41724/H [ 47…"}}
                result_1 = result;
                esp_1 = &result_1;
                
                if (result < 0)
                {
                    *edx[1] ^= *esi_2;
                    goto label_102;
                }
                
                esp_1 = (*(fsbase + (ebx_1 + 0x74)) * 0x3120726f);  {  // {"16 0 obj\r<</DecodeParms<</Colum…"}}
                *ebx_1[1] ^= *esi_2;
                int32_t eflags_12;
                char temp0_12;
                temp0_12 = __das(result, eflags_11);
                result = temp0_12;
                void* temp5_1 = ebp_2;
                ebp_2 += 1;
                esi_2 = __outsb(edx, *esi_2, esi_2, eflags_12);
                int16_t temp0_13;
                temp0_13 = __arpl_memw_gpr16(*(edx + 0x79), esi_2);  {  // {"obj\r<</DecodeParms<</Columns 4/…"}}
                *(edx + 0x79) = temp0_13;  {  // {"obj\r<</DecodeParms<</Columns 4/…"}}
                
                if ((temp5_1 + 1))
                {
                    result[ss] &= *edx[1];
                    goto label_125;
                }
                
                *result &= *ebx_1[1];
                *result &= *edx[1];
                *(edx + 0x2f) &= edx;  {  // {"/O 10/E 37847/N 1/T 41724/H [ 47…"}}
                cond:9_1 = esi_2 == 0xffffffff;
            }
            
            edi_1 = *esp_1;
            esi_2 = *(esp_1 + 4);
            ebp_2 = *(esp_1 + 8);
            ebx_1 = *(esp_1 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
            edx = *(esp_1 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
            ecx = *(esp_1 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
            result = *(esp_1 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
            
            if (cond:9_1)
            {
                *(esp_1 + 0x1c) = edx;  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                esp_1 += 0x1c;  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                char temp0_21;
                temp0_21 = __das(result, eflags_11);
                result = temp0_21;
                goto label_128;
            }
            
            esp_1 += 0x21;  {  // {"ized 1/L 42027/O 10/E 37847/N 1/…"}}
            int32_t eflags_13;
            int16_t temp0_14;
            temp0_14 = __arpl_memw_gpr16(*(gsbase + (edi_1 + 0x64)), ebp_2);  {  // {"              \r\n16 0 obj\r<</D…"}}
            *(gsbase + (edi_1 + 0x64)) = temp0_14;  {  // {"              \r\n16 0 obj\r<</D…"}}
            char temp0_15;
            temp0_15 = __das(result, eflags_13);
            result = temp0_15;
        }
        
        ecx -= 1;
        __return_addr_1 = *(esp_1 + 1);
        result ^= 0x30;  {  // {"O 10/E 37847/N 1/T 41724/H [ 477…"}}
        int32_t eflags_14;
        char temp0_16;
        temp0_16 = __aaa(result, *result[1], eflags_11);
        result = temp0_16;
        *result[1] = __return_addr_2;
        result ^= 0x36;  {  // {" 37847/N 1/T 41724/H [ 477 159]>…"}}
        esi_2 = (((esi_2 + 1) ^ *edx) + 1);
        char temp0_17;
        temp0_17 = __aaa(result, *result[1], eflags_14);
        result = temp0_17;
        *result[1] = __return_addr_2;
        *(esi_2 * 2);
        result = ((result ^ 0x39323443) ^ *(ebp_2 + 0x38));  {  // {"7847/N 1/T 41724/H [ 477 159]>>\r…"}}
        *(ebp_2 + 0x37) ^= result;  {  // {"37847/N 1/T 41724/H [ 477 159]>>…"}}
        void* edx_1;
        *edx_1[1] = (*(edx + 1)[1] ^ *result);
        *__return_addr_1;
        esp_1 += 6;
        *(ebp_2 + 0x43);  {  // {"41724/H [ 477 159]>>\rendobj\r  …"}}
        *result;
        edx = (edx_1 + 1);
        goto label_f8;
    }
    
    edx += 1;
label_f8:
    ebx_1 = (__return_addr_1 + 1);
    result ^= 0x41343541;
    *((edx + esi_2) + 0x36);  {  // {" 37847/N 1/T 41724/H [ 477 159]>…"}}
label_102:
    *result;
    uint16_t* esi_5 = (esi_2 ^ *(edi_1 + esi_2));
    edx += 1;
    int32_t eflags_15;
    char temp0_18;
    temp0_18 = __aaa(result, *result[1], eflags_11);
    result = temp0_18;
    *result[1] = __return_addr_2;
    *(ebx_1 + 0x3e);  {  // {" 1/T 41724/H [ 477 159]>>\rendob…"}}
    ebp_2 = *(esp_1 + 2);
    esp_1 += 6;
    char temp0_19;
    temp0_19 = __das(result, eflags_15);
    result = temp0_19;
    void* temp2_1 = ecx;
    ecx -= 1;
    uint16_t* esi_6 = __outsb(edx, *esi_5, esi_5, eflags_11);
    void* edx_2;
    void* esp_7;
    void* esp_12;
    char* esi_8;
    int16_t es;
    
    if ((temp2_1 - 1) < 0)
    {
        *(esp_1 - 4) = result;
        *(esp_1 - 8) = ecx;
        *(esp_1 - 0xc) = edx;
        *(esp_1 - 0x10) = ebx_1;  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
        *(esp_1 - 0x14) = (esp_1 - 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
        *(esp_1 - 0x18) = ebp_2;  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
        *(esp_1 - 0x1c) = esi_6;  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
        *(esp_1 - 0x20) = edi_1;  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
        esp_12 = (esp_1 - 0x20);  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
    label_173:
        *(esp_12 - 4) = result;
        *(esp_12 - 8) = ecx;
        *(esp_12 - 0xc) = edx;
        *(esp_12 - 0x10) = ebx_1;  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
        *(esp_12 - 0x14) = (esp_12 - 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
        *(esp_12 - 0x18) = ebp_2;  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
        *(esp_12 - 0x1c) = esi_6;  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
        *(esp_12 - 0x20) = edi_1;  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
        __bound_gprv_mema32((esp_12 - 0x20), *(result - 0x36));  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}  {  // {" 37847/N 1/T 41724/H [ 477 159]>…"}}
        *edx += edx;
        *(edi_1 - 0x7f) = ss;  {  // {"/DecodeParms<</Columns 4/Predict…"}}
        result = *(esp_12 - 0x20);  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
        char temp3_1 = result;
        result += *(ecx - 0x6fc4e4fc);
        bool c_2 = (temp3_1 + *(ecx - 0x6fc4e4fc)) < temp3_1;
        *(esp_12 - 0x20) = result;  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
        esp_7 = (esp_12 - 0x20);  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
        *edx[1] = 6;
        *ecx[1] = (*ecx[1] + *(esi_6 - 0x28bb7e81));
        *esi_6 |= result;
        esi_8 = (esi_6 + 1);
    label_197:
        char temp0_27 = ecx;
        ecx = *ecx[1];
        *ecx[1] = temp0_27;
        *(ebp_2 + 0xc);
        *(ebp_2 + 0xc) &= *edx[1];
        *((ebx_1 + edx) - 1) = es;
        int32_t temp9_1 = *edi_1;
        *edi_1 = (temp9_1 - ebp_2);
        bool o_2 = /* bool o_2 = unimplemented  {sbb dword [edi], ebp} */;
        bool cond:6_1;
        
        if ((temp9_1 - ebp_2) < 0 == o_2)
        {
            result |= 0x646e650a;
            cond:6_1 = result < 0;
            
            if (result < 0)
                goto label_1b2;
            
            *edi_1 = *esi_8;
        }
        else
        {
            *result |= *edx[1];
            edi_1[0xd0a09d7] += *ebx_1[1];
            *result[1] |= *(ebp_2 + 0x6e);  {  // {"    \r\n16 0 obj\r<</DecodeParms…"}}
            cond:6_1 = *result[1] < 0;
            
            if (*result[1] >= 0)
                *edi_1 = *esi_8;
            else
            {
            label_1b2:
                
                if (!(cond:6_1))
                {
                    int32_t edi_3 = *esp_7;
                    esi_8 = *(esp_7 + 4);
                    int32_t ebp_5 = *(esp_7 + 8);
                    ebx_1 = *(esp_7 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
                    edx_2 = *(esp_7 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
                    *(esp_7 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
                    int32_t eax_6 = *(esp_7 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                    esp_7 += 0x20;  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
                    int32_t* edi_4;
                    int32_t temp0_28;
                    temp0_28 = __insd(edi_3, edx_2, eflags_11);
                    *edi_4 = temp0_28;
                    __bound_gprv_mema32(ebp_5, *(edx_2 + 0xd));
                    *(edx_2 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                    *(edx_2 + 0x1c) = 0;  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                    result = ((eax_6 | 0x6f646e65) + 0xe09ce4);
                    goto label_23e;
                }
                
                *result[1] = 0xc1;  {  // {"Decode/ID[<6F4074632F7B9465C429E…"}}
                char temp13_1 = result;
                result += 0x20;  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
                *result;
                *(fsbase + (edx - 0x5bee7d6f)) = (RRCD(*(fsbase + (edx - 0x5bee7d6f)), ecx, temp13_1 >= 0xe0));  {  // {"E3E70E62093E><6D8EA8066BC5A54A9D…"}}
            }
        }
    }
    else
    {
        char temp0_20;
        temp0_20 = __aaa(result, *result[1], eflags_11);
        result = temp0_20;
        *result[1] = __return_addr_2;
        *edx &= *edx[1];
        *(ebp_2 + 0x2f) ^= ebx_1;  {  // {"/O 10/E 37847/N 1/T 41724/H [ 47…"}}
        ecx -= 1;
        uint16_t* esi_7 = __outsb(edx, *esi_6, esi_6, eflags_11);
        esi_2 = __outsw(edx, *esi_7, esi_7, eflags_11);
        *esi_2 &= *edx[1];
        *result &= *edx[1];
    label_125:
        *(edx + 0x2f) &= edx;  {  // {"/O 10/E 37847/N 1/T 41724/H [ 47…"}}
    label_128:
        esp_7 = (esp_1 - 1);
        esi_8 = __outsb(edx, *(gsbase + esi_2), esi_2, eflags_11);
        
        if (esp_1 == 1)
        {
            esi_8 = &esi_8[1];
            goto label_197;
        }
        
        *esi_8 &= *edx[1];
        void* temp10_1 = ebp_2;
        ebp_2 ^= *edi_1;
        bool z_1 = temp10_1 == *edi_1;
        *(esp_7 - 4) = result;
        esp_7 -= 4;
        
        if (z_1)
            goto label_157;
        
        result ^= 0x31;  {  // {" 10/E 37847/N 1/T 41724/H [ 477 …"}}
        char temp0_22;
        temp0_22 = __aaa(result, *result[1], eflags_11);
        result = temp0_22;
        *result[1] = __return_addr_2;
        *edx[1] ^= *0x6f6f522f;
        bool cond:15_1 = *edx[1] < 0;
        
        if (*edx[1] != 0)
        {
            *result;
            char temp16_1 = *result;
            *result ^= *result[1];
            bool s_1 = (temp16_1 ^ *result[1]) < 0;
            *(esp_7 - 4) = edx;
            char temp0_23;
            temp0_23 = __das(result, eflags_11);
            result = temp0_23;
            *(esp_7 - 8) = ebx_1;
            *(edx + 0x65);  {  // {"             \r\n16 0 obj\r<</De…"}}
            edi_1 = (*(edx + 0x65) * 0x2f383220);  {  // {"             \r\n16 0 obj\r<</De…"}}
            bool c_1 = /* bool c_1 = unimplemented  {imul edi, dword [edx+0x65], 0x2f383220} */;  {  // {"             \r\n16 0 obj\r<</De…"}}
            *(esp_7 - 0xc) = (esp_7 - 8);
            esp_7 -= 0xc;
            
            if (!(s_1))
            {
                if (s_1)
                {
                    edx_2 = (edx - 1);
                    result = (result - 0x15);  {  // {"bj\r<</Linearized 1/L 42027/O 10…"}}
                    result = __in_al_immb(0x9c, eflags_11);  {  // {"ictor 12>>/Encrypt 8 0 R/Filter/…"}}
                label_23e:
                    *ebx_1[1] |= *(edx_2 - 0x13);  {  // {" obj\r<</Linearized 1/L 42027/O …"}}
                    result &= *ebx_1[1];
                    *(esp_7 - 4) = 0x53;  {  // {"9]>>\rendobj\r                  …"}}
                    *esi_8;
                    /* undefined */;
                }
                
                result |= 0x300a;
                esi_8 = &esi_8[1];
                result = ((result | 0x4525250a) | 0x2020200a);
                *result &= *result[1];
                *result &= *result[1];
            }
            else
            {
                char temp0_24;
                temp0_24 = __das(result, eflags_11);
                result = temp0_24;
                result = *esp_7;
                *esp_7 = edx;
            label_157:
                char temp0_25;
                temp0_25 = __das(result, eflags_11);
                result = temp0_25;
                *(esp_7 - 4) = edi_1;
                int32_t ebx_2 = *(esp_7 - 4);
                *result ^= esp_7;
                *result[1] ^= *result;
                int32_t temp12_1 = (*(ebp_2 + 0x3e) ^ ebx_2);  {  // {" 1/T 41724/H [ 477 159]>>\rendob…"}}
                *(ebp_2 + 0x3e) = temp12_1;  {  // {" 1/T 41724/H [ 477 159]>>\rendob…"}}
                cond:15_1 = temp12_1 < 0;
                
                if (temp12_1 < 0)
                {
                label_166:
                    
                    if (!(cond:15_1))
                    {
                        esi_6 = *(esp_7 + 4);
                        ebp_2 = *(esp_7 + 8);
                        ebx_1 = *(esp_7 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
                        edx = *(esp_7 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
                        ecx = *(esp_7 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
                        int32_t eax_5 = *(esp_7 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                        esp_12 = (esp_7 + 0x20);  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
                        int32_t temp0_26;
                        temp0_26 = __insd(*esp_7, edx, eflags_11);
                        *edi_1 = temp0_26;
                        result = (eax_5 | 0x62de680a);
                        __bound_gprv_mema32(esp_12, *((result + edx) + 0x60));  {  // {"                  \r\n16 0 obj\r…"}}
                        goto label_173;
                    }
                    
                    result &= 0xd464f45;
                    *result[1] |= *result;
                    *result &= *result[1];
                    *result &= *result[1];
                    *result &= *result[1];
                }
            }
        }
        else if (*edx[1] < 0)
            goto label_166;
        
        *0x2037320a &= ecx;
        *result ^= *result[1];
        int32_t esi_9 = __outsd(edx, *esi_8, esi_8, eflags_11);
        __bound_gprv_mema32(ebp_2, *(edx + 0xd));
        int32_t eflags_16;
        char temp0_29;
        temp0_29 = __das(result, eflags_11);
        result = temp0_29;
        char* edi_6 = *esp_7;
        char* esi_10 = *(esp_7 + 4);
        void* ebp_6 = *(esp_7 + 8);
        char* ebx_3 = *(esp_7 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
        void* edx_3 = *(esp_7 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
        int32_t* ecx_2 = *(esp_7 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
        int32_t eax_9 = *(esp_7 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
        void* esp_23;
        void* esi_13;
        bool c_4;
        
        if (esi_9 == 0xffffffff)
        {
            *(esp_7 + 0x1c) = edx_3;  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
            esp_23 = (esp_7 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
            *(esi_10 + 0x57100987) &= edx_3;
            c_4 = false;
            esi_13 = __outsb(edx_3, *(gsbase + esi_10), esi_10, eflags_16);
            *((edx_3 << 3) + 0x3f34df61);
            goto label_2eb;
        }
        
        int32_t eflags_17;
        int16_t temp0_30;
        temp0_30 = __arpl_memw_gpr16(*(gsbase + (edi_6 + 0x64)), ebp_6);  {  // {"              \r\n16 0 obj\r<</D…"}}
        *(gsbase + (edi_6 + 0x64)) = temp0_30;  {  // {"              \r\n16 0 obj\r<</D…"}}
        char temp0_31;
        temp0_31 = __das(eax_9, eflags_17);
        eax_9 = temp0_31;
        ecx_2 -= 1;
        *edi_6 &= *edx_3[1];
        char* eax_10 = (eax_9 ^ 0x6e654c2f);
        bool z_2 = eax_9 == 0x6e654c2f;
        int32_t* esp_20;
        void* esp_29;
        void* esi_21;
        void* esi_24;
        int16_t ds;
        bool c_5;
        bool p_2;
        bool a_2;
        bool z_4;
        bool s_4;
        
        if (z_2)
        {
            if (!(z_2))
            {
                esi_10 = *(esp_7 + 0x25);  {  // {" 1/L 42027/O 10/E 37847/N 1/T 41…"}}
                ebp_6 = *(esp_7 + 0x29);  {  // {" 42027/O 10/E 37847/N 1/T 41724/…"}}
                ebx_3 = *(esp_7 + 0x31);  {  // {" 10/E 37847/N 1/T 41724/H [ 477 …"}}
                edx_3 = *(esp_7 + 0x35);  {  // {"E 37847/N 1/T 41724/H [ 477 159]…"}}
                ecx_2 = *(esp_7 + 0x39);  {  // {"847/N 1/T 41724/H [ 477 159]>>\r…"}}
                void* eax_14 = *(esp_7 + 0x3d);  {  // {"N 1/T 41724/H [ 477 159]>>\rendo…"}}
                esp_20 = (esp_7 + 0x41);  {  // {"T 41724/H [ 477 159]>>\rendobj\r…"}}
                int32_t temp0_34;
                temp0_34 = __insd(*(esp_7 + 0x21), edx_3, eflags_16);  {  // {"ized 1/L 42027/O 10/E 37847/N 1/…"}}
                *edi_6 = temp0_34;
                eax_10 = (eax_14 | 0x6f646e65);
                __bound_gprv_mema32(ebp_6, *(edx_3 + 0xd));
                goto label_27c;
            }
            
            *eax_10[1] u>>= 1;
            c_4 = false;
            edi_6 = *(esp_7 + 0x21);  {  // {"ized 1/L 42027/O 10/E 37847/N 1/…"}}
            esi_13 = *(esp_7 + 0x25);  {  // {" 1/L 42027/O 10/E 37847/N 1/T 41…"}}
            ebp_6 = *(esp_7 + 0x29);  {  // {" 42027/O 10/E 37847/N 1/T 41724/…"}}
            ebx_3 = *(esp_7 + 0x31);  {  // {" 10/E 37847/N 1/T 41724/H [ 477 …"}}
            edx_3 = *(esp_7 + 0x35);  {  // {"E 37847/N 1/T 41724/H [ 477 159]…"}}
            ecx_2 = *(esp_7 + 0x39);  {  // {"847/N 1/T 41724/H [ 477 159]>>\r…"}}
            *(esp_7 + 0x3d);  {  // {"N 1/T 41724/H [ 477 159]>>\rendo…"}}
            esp_23 = (esp_7 + 0x41);  {  // {"T 41724/H [ 477 159]>>\rendobj\r…"}}
        label_2e8:
            *(edi_6 * 2) = __fbst(arg8);
        label_2eb:
            int32_t esp_33 = (esp_23 - esp_23);
            eax_10 = __lds_gprz_memp(*(ebp_6 + 0x1a));  {  // {"/Linearized 1/L 42027/O 10/E 378…"}}
            eax_10 = __in_al_dx(edx_3, eflags_16);
            *(esp_33 - 4) = edx_3;
            esp_23 = (esp_33 - 4);
            __bound_gprv_mema32(esi_13, *(ebx_3 + 0x4a));  {  // {" [ 477 159]>>\rendobj\r         …"}}
        label_2f5:
            eax_10 = __in_al_immb(0x60, eflags_16);  {  // {"                  \r\n16 0 obj\r…"}}
            void* temp22_1 = esi_13;
            int32_t temp23_1 = *ecx_2;
            esi_13 &= *ecx_2;
            bool p_1 = /* bool p_1 = unimplemented  {and esi, dword [ecx]} */;
            bool a_1 = /* undefined */;
            bool d;
            *(esp_23 - 4) = ((((0) ? 1 : 0) << 0xb) | ((((d) ? 1 : 0) << 0xa) | (((((temp22_1 & temp23_1) < 0) ? 1 : 0) << 7) | (((((temp22_1 & temp23_1) == 0) ? 1 : 0) << 6) | ((((a_1) ? 1 : 0) << 4) | ((((p_1) ? 1 : 0) << 2) | ((0) ? 1 : 0)))))));
            *ecx_2[1] -= *ecx_2;
            int32_t eflags_21;
            char temp0_48;
            temp0_48 = __das(eax_10, eflags_16);
            eax_10 = temp0_48;
            *(esp_23 - 8) = eax_10;
            *0x38323031 &= *ecx_2[1];
            char temp0_49;
            temp0_49 = __das(eax_10, eflags_21);
            eax_10 = temp0_49;
            *(esp_23 - 0xc) = edx_3;
            char temp24_1 = *(edi_6 + ebp_6);
            *(edi_6 + ebp_6) &= *edx_3[1];
            c_5 = false;
            /* unimplemented  {and byte [edi+ebp], dh} */;
            /* undefined */;
            *(esp_23 - 0x10) = ebx_3;  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
            esp_23 -= 0x10;  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
            
            if ((temp24_1 & *edx_3[1]) != 0)
                goto label_30c;
            
            char temp0_59;
            temp0_59 = __das(eax_10, eflags_16);
            eax_10 = temp0_59;
        label_37c:
            p_2 = /* p_2 = unimplemented  {inc ebx} */;
            a_2 = /* a_2 = unimplemented  {inc ebx} */;
            z_4 = ebx_3 == 0xffffffff;
            s_4 = &ebx_3[1] < 0;
            edi_6 = *esp_23;
            esi_21 = *(esp_23 + 4);
            ebp_6 = *(esp_23 + 8);
            ebx_3 = *(esp_23 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
            edx_3 = *(esp_23 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
            ecx_2 = *(esp_23 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
            eax_10 = *(esp_23 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
            esp_29 = (esp_23 + 0x20);  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
            
            if (z_4)
                goto label_3e1;
            
        label_380:
            uint8_t temp0_60;
            temp0_60 = __insb(edi_6, edx_3, eflags_16);
            *edi_6 = temp0_60;
            esi_24 = __outsd(edx_3, *esi_21, esi_21, eflags_16);
            eax_10 |= 0x6f646e65;
            goto label_38a;
        }
        
        *eax_10 &= *ebx_3[1];
        *edi_6 ^= *ecx_2[1];
        *(esp_7 + 0x1d) = ebx_3;  {  // {"nearized 1/L 42027/O 10/E 37847/…"}}
        esp_20 = (esp_7 + 0x1d);  {  // {"nearized 1/L 42027/O 10/E 37847/…"}}
        *ebx_3 &= *edx_3[1];
        char temp20_1 = *esi_10;
        
        if (temp20_1 >= *ebx_3[1])
            goto label_287;
        
        if (temp20_1 < *ebx_3[1])
        {
            *(esp_20 - 4) = 0xd;
            esp_20 -= 4;
        label_27c:
            *eax_10;
            *eax_10 ^= *eax_10[1];
            esi_10 = __outsd(edx_3, *esi_10, esi_10, eflags_16);
            __bound_gprv_mema32(ebp_6, *(edx_3 + 0xd));
            char temp0_35;
            temp0_35 = __das(eax_10, eflags_16);
            eax_10 = temp0_35;
        label_287:
            ebx_3 = &ebx_3[1];
            esi_13 = &esi_10[1];
            bool cond:22_1 = eax_10 == 0x3c;  {  // {"/N 1/T 41724/H [ 477 159]>>\rend…"}}
            bool cond:25_1 = eax_10 >= 0x3c;  {  // {"/N 1/T 41724/H [ 477 159]>>\rend…"}}
            char temp0_36;
            temp0_36 = __das(eax_10, eflags_16);
            eax_10 = temp0_36;
            *(esp_20 - 4) = ebx_3;
            esp_23 = (esp_20 - 4);
            
            if (cond:22_1)
            {
                if (cond:25_1)
                    goto label_33f;
                
                goto label_2f5;
            }
            
            ebx_3 = &ebx_3[1];
            esi_13 += 1;
            c_5 = eax_10 < 0x3c;  {  // {"/N 1/T 41724/H [ 477 159]>>\rend…"}}
            char temp0_37;
            temp0_37 = __das(eax_10, eflags_16);
            eax_10 = temp0_37;
            int32_t* temp26_1 = ecx_2;
            ecx_2 += 1;
            int32_t eflags_23;
            
            if (temp26_1 == 0xffffffff)
            {
                *(esp_23 - 4) = 0x6e657645;
                esp_23 -= 4;
                
                if (temp26_1 != 0xffffffff)
                {
                    int32_t esi_14 = __outsd(edx_3, *esi_13, esi_13, eflags_16);
                    int32_t eflags_18;
                    int16_t temp0_38;
                    temp0_38 = __arpl_memw_gpr16(*(edi_6 + 0x70), ecx_2);  {  // {"  \r\n16 0 obj\r<</DecodeParms<<…"}}
                    *(edi_6 + 0x70) = temp0_38;  {  // {"  \r\n16 0 obj\r<</DecodeParms<<…"}}
                    int32_t esi_15 = __outsb(edx_3, *(gsbase + esi_14), esi_14, eflags_18);
                    int32_t eflags_19;
                    char temp0_39;
                    temp0_39 = __das(eax_10, eflags_18);
                    eax_10 = temp0_39;
                    ebx_3 = &ebx_3[1];
                    char temp0_40;
                    temp0_40 = __das(eax_10, eflags_19);
                    eax_10 = temp0_40;
                    *(esp_23 - 3) = ebx_3;
                    *(esp_23 - 7) = (esi_15 + 1);
                    *ecx_2[1] = (*(ecx_2 + 1)[1] ^ *edi_6);
                    esp_29 = (esp_23 - 8);
                    esi_13 = __outsb(edx_3, *(gsbase + (esi_15 + 1)), (esi_15 + 1), eflags_16);
                    
                    if (esp_23 == 8)
                        goto label_31e;
                    
                    *ecx_2 &= *edx_3[1];
                    char temp0_41;
                    temp0_41 = __das(eax_10, eflags_16);
                    eax_10 = temp0_41;
                    *((esp_29 + ((esi_13 + 1) << 1)) + 0x65);  {  // {"             \r\n16 0 obj\r<</De…"}}
                    bool c_6 = /* bool c_6 = unimplemented  {imul ebp, dword [esp+esi*2+0x65], 0x74532f72} */;  {  // {"             \r\n16 0 obj\r<</De…"}}
                    uint16_t* esi_18 = *(esp_29 + 4);
                    __outsb(*(esp_29 + 0x14), *esi_18, esi_18, eflags_16);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
                    edi_6 = *(esp_29 + 0x20);  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
                    esi_13 = *(esp_29 + 0x24);  {  // {"d 1/L 42027/O 10/E 37847/N 1/T 4…"}}
                    ebp_6 = *(esp_29 + 0x28);  {  // {"L 42027/O 10/E 37847/N 1/T 41724…"}}
                    ebx_3 = *(esp_29 + 0x30);  {  // {"O 10/E 37847/N 1/T 41724/H [ 477…"}}
                    edx_3 = *(esp_29 + 0x34);  {  // {"/E 37847/N 1/T 41724/H [ 477 159…"}}
                    ecx_2 = *(esp_29 + 0x38);  {  // {"7847/N 1/T 41724/H [ 477 159]>>\r…"}}
                    eax_10 = *(esp_29 + 0x3c);  {  // {"/N 1/T 41724/H [ 477 159]>>\rend…"}}
                    esp_23 = (esp_29 + 0x40);  {  // {"/T 41724/H [ 477 159]>>\rendobj\r…"}}
                    
                    if (c_6)
                        goto label_333;
                }
                
                char temp0_42;
                temp0_42 = __das(eax_10, eflags_16);
                eax_10 = temp0_42;
                void* temp31_1 = esp_23;
                esp_23 -= 1;
                esi_13 = __outsb(edx_3, *(gsbase + esi_13), esi_13, eflags_23);
                
                if (temp31_1 == 1)
                {
                    *eax_10 += eax_10;
                    *eax_10 += eax_10;
                    *eax_10 += eax_10;
                    *edi_6 -= ebp_6;
                    goto label_344;
                }
                
                *ecx_2 &= *edx_3[1];
                *ebx_3[1] ^= *eax_10;
                int32_t eflags_20;
                char temp0_43;
                temp0_43 = __das(eax_10, eflags_23);
                eax_10 = temp0_43;
                edi_6 -= 1;
                char temp25_1 = *(ebp_6 - 0x66);  {  // {"            \r\n16 0 obj\r<</Dec…"}}
                *(ebp_6 - 0x66) -= *ebx_3[1];  {  // {"            \r\n16 0 obj\r<</Dec…"}}
                c_4 = temp25_1 < *ebx_3[1];
                /* unimplemented  {enter 0xdcd0, 0x24} */;  {  // {"d 1/L 42027/O 10/E 37847/N 1/T 4…"}}
                char temp0_44;
                temp0_44 = __aad_immb(0x61, 0x87, 0);  {  // {"                 \r\n16 0 obj\r<…"}}  {  // {"arms<</Columns 4/Predictor 12>>/…"}}
                int32_t eax_15;
                eax_15 = temp0_44;
                *eax_15[1] = __return_addr_2;
                goto label_2e8;
            }
            
            int32_t temp0_50;
            temp0_50 = __insd(edi_6, edx_3, eflags_16);
            *edi_6 = temp0_50;
        label_30c:
            esi_24 = (esi_13 + 1);
            bool s_5 = (esi_13 + 1) < 0;
            char temp0_51;
            temp0_51 = __das(eax_10, eflags_16);
            eax_10 = temp0_51;
            *(esp_23 - 4) = ebx_3;
            int32_t eflags_24;
            char eax_21;
            bool z_7;
            
            if (esi_13 == 0xffffffff)
            {
                *(esp_23 - 8) = edx_3;
                esp_29 = (esp_23 - 8);
            label_376:
                char temp0_57;
                temp0_57 = __das(eax_10, eflags_16);
                eax_10 = temp0_57;
                *(esp_29 - 4) = esp_29;
                esp_23 = (esp_29 - 4);
                
                if (s_5)
                {
                    char temp0_58;
                    temp0_58 = __das(eax_10, eflags_24);
                    eax_10 = temp0_58;
                    goto label_37c;
                }
                
                *eax_10 &= *edx_3[1];
                char temp37_1 = *(edx_3 + 0x2f);  {  // {"/O 10/E 37847/N 1/T 41724/H [ 47…"}}
                *(edx_3 + 0x2f) &= edx_3;  {  // {"/O 10/E 37847/N 1/T 41724/H [ 47…"}}
                z_7 = (temp37_1 & edx_3) == 0;
            label_3ef:
                *(esp_23 - 4) = edx_3;
                esp_23 -= 4;
            label_4d8:
                
                if (!(z_7))
                {
                    ebx_3 = 0xf7;  {  // {"BC5A54A9D2698D347D6B79C>]/Index[…"}}
                    int32_t eflags_31;
                    char temp0_83;
                    temp0_83 = __aad_immb(0x84, eax_10, *eax_10[1]);  {  // {"deParms<</Columns 4/Predictor 12…"}}
                    eax_10 = temp0_83;
                    *eax_10[1] = __return_addr_2;
                    /* undefined */;
                }
                
                eax_21 = (eax_10 - 0x6048e2a7);
            }
            else
            {
                ebx_3 = &ebx_3[1];
                char temp0_52;
                temp0_52 = __das(eax_10, eflags_16);
                eax_10 = temp0_52;
                *(esp_23 - 8) = ebx_3;
                esp_29 = (esp_23 - 8);
                char* cs;
                
                if (esi_24 == 0xffffffff)
                {
                    esi_24 = __outsd(edx_3, *(esi_24 + 1), (esi_24 + 1), eflags_16);
                label_38a:
                    __bound_gprv_mema32(ebp_6, *(edx_3 + 0xd));
                    *eax_10 ^= esi_24;
                    *eax_10 &= *edx_3[1];
                label_391:
                    edi_6[0x62] &= *ecx_2[1];  {  // {"                \r\n16 0 obj\r<<…"}}
                    *(esp_29 - 4) = 0xd;
                    esp_23 = (esp_29 - 4);
                    bool c_8 = eax_10 < 0x3c;  {  // {"/N 1/T 41724/H [ 477 159]>>\rend…"}}
                    char temp0_61;
                    temp0_61 = __das(eax_10, eflags_16);
                    eax_10 = temp0_61;
                    void* ebx_5 = &ebx_3[1];
                    bool z_6 = ebx_3 == 0xffffffff;
                    uint16_t* esi_25 = __outsd(edx_3, *esi_24, esi_24, eflags_24);
                    uint16_t* esi_26 = __outsb(edx_3, *esi_25, esi_25, eflags_24);
                    char* eax_18;
                    bool c_11;
                    
                    if (!(z_6))
                    {
                        esi_24 = __outsb(edx_3, *esi_26, esi_26, eflags_24);
                        
                        if (z_6)
                        {
                            eax_18 = (eax_10 | 0x6f646e65);
                        label_419:
                            __bound_gprv_mema32(ebp_6, *(edx_3 + 0xd));
                            *ecx_2 ^= esi_24;
                            *eax_18 &= *edx_3[1];
                            edi_6[0x62] &= *ecx_2[1];  {  // {"                \r\n16 0 obj\r<<…"}}
                            *(esp_23 - 4) = 0xd;
                            int32_t eflags_26;
                            char temp0_72;
                            temp0_72 = __das(eax_18, eflags_24);
                            eax_18 = temp0_72;
                            edi_6 = *(esp_23 - 4);
                            ebp_6 = *(esp_23 + 4);
                            ebx_3 = *(esp_23 + 0xc);
                            edx_3 = *(esp_23 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
                            ecx_2 = *(esp_23 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
                            eax_10 = *(esp_23 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
                            
                            if (esi_24 == 0xffffffff)
                            {
                                eax_10 = (eax_10 * *ebx_3);
                                int32_t eflags_29;
                                int16_t temp0_80;
                                temp0_80 = __arpl_memw_gpr16(*(ebp_6 + 9), ebx_3);
                                *(ebp_6 + 9) = temp0_80;
                                trap(0x7f);  {  // {"/DecodeParms<</Columns 4/Predict…"}}
                            }
                            
                            void* esp_51 = (esp_23 + 0x1d);  {  // {"nearized 1/L 42027/O 10/E 37847/…"}}
                            int32_t eflags_27;
                            int16_t temp0_73;
                            temp0_73 = __arpl_memw_gpr16(*(gsbase + (edi_6 + 0x64)), ebp_6);  {  // {"              \r\n16 0 obj\r<</D…"}}
                            *(gsbase + (edi_6 + 0x64)) = temp0_73;  {  // {"              \r\n16 0 obj\r<</D…"}}
                            int32_t eflags_28;
                            char temp0_74;
                            temp0_74 = __das(eax_10, eflags_27);
                            eax_10 = temp0_74;
                            int32_t esi_28 = (*(edx_3 + 0x73) * 0x32372074);  {  // {"\n16 0 obj\r<</DecodeParms<</Col…"}}
                            char temp0_75;
                            temp0_75 = __das(eax_10, eflags_28);
                            eax_10 = temp0_75;
                            esp_23 = (esp_51 - 1);
                            esi_24 = __outsb(edx_3, *(gsbase + esi_28), esi_28, eflags_24);
                            
                            if (esp_51 != 1)
                            {
                                *ecx_2 &= *edx_3[1];
                                *eax_10 ^= *edx_3[1];
                                *edi_6;
                                goto label_450;
                            }
                            
                            /* unimplemented  {fdiv st0, qword [edi+0x34]} */;  {  // {"/E 37847/N 1/T 41724/H [ 477 159…"}}
                            char temp60_1 = ebx_3;
                            ebx_3 -= *ecx_2[1];
                            c_11 = temp60_1 < *ecx_2[1];
                            __bound_gprv_mema32(edx_3, *(eax_10 - 0x15));  {  // {"bj\r<</Linearized 1/L 42027/O 10…"}}
                            int16_t x87status_1;
                            int16_t temp0_82;
                            temp0_82 = __fnstcw_memmem16(arg7);
                            ecx_2[-0x1191794d] = temp0_82;
                            
                            if ((temp60_1 - *ecx_2[1]) >= 0)
                            {
                                esp_23 = (RRCD(esp_23, 0x16, c_11));  {  // {"j\r<</Linearized 1/L 42027/O 10/…"}}
                                eax_10 += *(ebp_6 + 0x7f);  {  // {"/DecodeParms<</Columns 4/Predict…"}}
                                *ecx_2[1] = *(gsbase + ((esi_24 + (ebp_6 << 1)) + 0x3bb0f4cd));
                                goto label_527;
                            }
                            
                            eax_10 = 0xed9b5647();
                        label_521:
                            *eax_10[1] = (*eax_10[1] + *ebx_3[1]);
                            *edi_6;
                            goto label_527;
                        }
                        
                        *ecx_2 &= *edx_3[1];
                        *eax_10[1] ^= *eax_10;
                        *eax_10;
                        *eax_10 ^= *eax_10[1];
                        *(esp_23 - 4) = edx_3;
                        esp_23 -= 4;
                        char temp0_62;
                        temp0_62 = __das(eax_10, eflags_24);
                        eax_10 = temp0_62;
                        ebx_3 = (ebx_5 + 1);
                        z_7 = ebx_5 == 0xffffffff;
                        
                        if ((ebx_5 + 1))
                            goto label_4d8;
                        
                        __outsd(edx_3, *esi_24, esi_24, eflags_24);
                        
                        if ((ebx_5 + 1) < 0)
                            goto label_40c;
                        
                        *eax_10 ^= *eax_10[1];
                        *eax_10 ^= *eax_10[1];
                        eax_10 ^= 0x322e3539;
                        char temp0_63;
                        temp0_63 = __aaa(eax_10, *eax_10[1], eflags_24);
                        eax_10 = temp0_63;
                        *eax_10[1] = __return_addr_2;
                        eax_10[ss] &= *ebx_3[1];
                        eax_10 ^= 0x31;  {  // {" 10/E 37847/N 1/T 41724/H [ 477 …"}}
                        *(cs + ecx_2);
                        goto label_3c3;
                    }
                    
                    edi_6 = *esp_23;
                    esi_24 = *(esp_23 + 4);
                    ebp_6 = *(esp_23 + 8);
                    ebx_3 = *(esp_23 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
                    edx_3 = *(esp_23 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
                    ecx_2 = *(esp_23 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
                    eax_10 = *(esp_23 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                    esp_23 += 0x20;  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
                    
                    if (z_6)
                    {
                        ebp_6 = *esp_23;
                        *esp_23 = esi_24;
                        *(esp_23 - 4) = ds;
                        esp_23 -= 4;
                        ecx_2 = (ecx_2 - *(esi_24 - 0x7ff719d9));
                        edi_6 = *(edi_6 * 2);
                        char temp59_1 = *ecx_2[1];
                        *ecx_2[1] += *ebx_3[1];
                        p_2 = /* p_2 = unimplemented  {add ch, bh} */;
                        a_2 = /* a_2 = unimplemented  {add ch, bh} */;
                        z_4 = temp59_1 == -(*ebx_3[1]);
                        s_4 = (temp59_1 + *ebx_3[1]) < 0;
                        eax_10 = *(esp_23 + (ebp_6 << 2));
                    }
                    else
                    {
                        char temp54_1 = *eax_10;
                        *eax_10 &= *edx_3[1];
                        p_2 = /* p_2 = unimplemented  {and byte [eax], dh} */;
                        a_2 = /* undefined */;
                        z_4 = (temp54_1 & *edx_3[1]) == 0;
                        s_4 = (temp54_1 & *edx_3[1]) < 0;
                        char temp0_70;
                        temp0_70 = __das(eax_10, eflags_24);
                        eax_10 = temp0_70;
                    label_409:
                        *(esp_23 - 4) = esp_23;
                        esp_23 -= 4;
                        
                        if (s_4)
                        {
                        label_40c:
                            char temp0_71;
                            temp0_71 = __das(eax_10, eflags_24);
                            eax_10 = temp0_71;
                            *(esp_23 - 4) = eax_10;
                            edi_6 = *(esp_23 - 4);
                            esi_24 = *esp_23;
                            ebp_6 = *(esp_23 + 4);
                            *(esp_23 + 0xc);
                            edx_3 = *(esp_23 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
                            ecx_2 = *(esp_23 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
                            void* eax_17 = *(esp_23 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
                            esp_23 += 0x1c;  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                            eax_18 = (eax_17 | 0x6f646e65);
                            goto label_419;
                        }
                    }
                    
                    *(edi_6 + 0x21f52e02);
                    char* ecx_4 = (*(edi_6 + 0x21f52e02) * 0x1130bbd4);
                    bool c_10 = /* bool c_10 = unimplemented  {imul ecx, dword [edi+0x21f52e02], 0x1130bbd4} */;
                    void* temp47_1;
                    
                    while (true)
                    {
                        *eax_10[1] = ((((s_4) ? 1 : 0) << 7) | ((((z_4) ? 1 : 0) << 6) | ((((a_2) ? 1 : 0) << 4) | ((((p_2) ? 1 : 0) << 2) | ((c_10) ? 1 : 0)))));
                        temp47_1 = esp_23;
                        esp_23 -= 1;
                        
                        if (ecx_4 != 0)
                            break;
                        
                        char temp0_79;
                        temp0_79 = __aam_immb(0xbb, eax_10);  {  // {"/FlateDecode/ID[<6F4074632F7B946…"}}
                        eax_10 = temp0_79;
                        *eax_10[1] = __return_addr_2;
                        char temp50_1 = *ecx_4;
                        *ecx_4 ^= edx_3;
                        c_10 = false;
                        p_2 = /* p_2 = unimplemented  {xor byte [ecx], dl} */;
                        a_2 = /* undefined */;
                        z_4 = temp50_1 == edx_3;
                        s_4 = (temp50_1 ^ edx_3) < 0;
                    }
                    
                    if ((temp47_1 != 1 && !(c_10)))
                    {
                        int32_t eflags_32;
                        int16_t temp0_84;
                        temp0_84 = __arpl_memw_gpr16(*(edx_3 - 0x3e8b05fc), edx_3);
                        *(edx_3 - 0x3e8b05fc) = temp0_84;
                        /* undefined */;
                    }
                    
                    ecx_4 = 0x31;  {  // {" 10/E 37847/N 1/T 41724/H [ 477 …"}}
                    __in_oeax_immb(0x5b, eflags_24);  {  // {"obj\r                   \r\n16 0…"}}
                    
                    if ((temp47_1 - 1) < 0)
                        /* undefined */;
                    
                    int32_t eax_20;
                    int32_t ecx_5;
                    eax_20 = 0xb702cfde();
                    esp_23 &= *(ebx_3 + 0x5d);  {  // {"j\r                   \r\n16 0 o…"}}
                    ebp_6 |= ecx_5;
                    
                    if (ebp_6 > 0)
                    {
                        c_11 = eax_20 < 0x9b5126e8;
                        eax_10 = __in_oeax_dx(edx_3, eflags_24);
                        goto label_521;
                    }
                    
                    *(esp_23 - 4) = ecx_5;
                    *(esp_23 - 4);
                    int32_t eflags_30;
                    char temp0_81;
                    temp0_81 = __daa(eax_20, eflags_24);
                    eax_20 = temp0_81;
                    (*esi_24 - *edi_6);
                    /* jump -> 0xc3cf7521 */
                }
                
                esi_21 = (esi_24 + 2);
                char temp0_53;
                temp0_53 = __das(eax_10, eflags_16);
                eax_10 = temp0_53;
                *(esp_29 - 4) = ebx_3;
                esp_29 -= 4;
                
                if (esi_24 == 0xfffffffe)
                    goto label_380;
                
                ebx_3 = &ebx_3[1];
                esi_13 = (esi_21 + 1);
            label_31e:
                int32_t eflags_22;
                char temp0_54;
                temp0_54 = __das(eax_10, eflags_16);
                eax_10 = temp0_54;
                *(esp_29 - 4) = ebp_6;
                char temp35_1 = *(edx_3 - 0x60840049);
                *(edx_3 - 0x60840049) -= *ebx_3[1];
                eflags_16 = __cli(eflags_22);
                ebx_3 = (ebx_3 + *((esi_13 + (ebp_6 << 1)) - 0x34));  {  // {"/E 37847/N 1/T 41724/H [ 477 159…"}}
                (/* unimplemented  {fcomp st0, st0} f- unimplemented  {fcomp st0, st0} */ - /* unimplemented  {fcomp st0, st0} f- unimplemented  {fcomp st0, st0} */);
                /* unimplemented  {fcomp st0, st0} */;
                *ecx_2[1] = 0xd7;  {  // {"B9465C429E3E70E62093E><6D8EA8066…"}}
                ds = *(esp_29 - 4);
                esp_23 = (esp_29 - 2);
                edi_6 = esi_13;
            label_333:
                *eax_10 += eax_10;
                *eax_10 += eax_10;
                *eax_10 += eax_10;
                *eax_10 += eax_10;
                *eax_10 += eax_10;
                *eax_10 += eax_10;
            label_33f:
                *eax_10 += eax_10;
                *ecx_2 += *ecx_2[1];
                char temp0_55;
                temp0_55 = __das(eax_10, eflags_16);
                eax_10 = temp0_55;
            label_344:
                *(esp_23 - 4) = esi_13;
                esp_23 -= 4;
                *(esi_13 + edi_6) &= *edx_3[1];
                eax_10 |= 0x6f646e65;
                __bound_gprv_mema32(ebp_6, *(edx_3 + 0xd));
                *eax_10;
                *eax_10 ^= *eax_10[1];
                __outsd(edx_3, *esi_13, esi_13, eflags_23);
                __bound_gprv_mema32(ebp_6, *(edx_3 + 0xd));
                char temp0_56;
                temp0_56 = __das(eax_10, eflags_23);
                eax_10 = temp0_56;
                
                if (ebp_6 != 1)
                {
                    *esp_23;
                    *(esp_23 + 4);
                    *(esp_23 + 8);
                    ebx_3 = *(esp_23 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
                    edx_3 = *(esp_23 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
                    ecx_2 = *(esp_23 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
                    eax_10 = *(esp_23 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                    
                    if (ebp_6 == 1)
                        goto label_3c6;
                    
                    *ecx_2 &= *edx_3[1];
                    *eax_10 &= *edx_3[1];
                    char temp39_1 = (*(edx_3 + 0x2f) & edx_3);  {  // {"/O 10/E 37847/N 1/T 41724/H [ 47…"}}
                    *(edx_3 + 0x2f) = temp39_1;  {  // {"/O 10/E 37847/N 1/T 41724/H [ 47…"}}
                    *(esp_23 + 0x1c) = eax_10;  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                    edi_6 = *(esp_23 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                    esi_24 = *(esp_23 + 0x20);  {  // {"rized 1/L 42027/O 10/E 37847/N 1…"}}
                    ebp_6 = *(esp_23 + 0x24);  {  // {"d 1/L 42027/O 10/E 37847/N 1/T 4…"}}
                    ebx_3 = *(esp_23 + 0x2c);  {  // {"027/O 10/E 37847/N 1/T 41724/H […"}}
                    edx_3 = *(esp_23 + 0x30);  {  // {"O 10/E 37847/N 1/T 41724/H [ 477…"}}
                    ecx_2 = *(esp_23 + 0x34);  {  // {"/E 37847/N 1/T 41724/H [ 477 159…"}}
                    eax_10 = *(esp_23 + 0x38);  {  // {"7847/N 1/T 41724/H [ 477 159]>>\r…"}}
                    esp_29 = (esp_23 + 0x3c);  {  // {"/N 1/T 41724/H [ 477 159]>>\rend…"}}
                    
                    if (temp39_1 >= 0)
                        goto label_391;
                    
                    char* temp43_1 = eax_10;
                    eax_10 ^= 0x52203020;
                    c_5 = false;
                    s_5 = (temp43_1 ^ 0x52203020) < 0;
                    goto label_376;
                }
                
                *ecx_2;
            label_3c3:
                *esp_23;
                char temp0_64;
                temp0_64 = __das(eax_10, eflags_16);
                eax_10 = temp0_64;
            label_3c6:
                esp_23 = (*(fsbase + (ecx_2 + 0x42)) * 0x305b786f);  {  // {" 41724/H [ 477 159]>>\rendobj\r …"}}
                *eax_10 &= *edx_3[1];
                *0x322e3539 &= *edx_3[1];
                char temp0_65;
                temp0_65 = __aaa(eax_10, *eax_10[1], eflags_16);
                eax_10 = temp0_65;
                *eax_10[1] = __return_addr_2;
                eax_10[ss] &= *ebx_3[1];
                eax_10 ^= 0x31;  {  // {" 10/E 37847/N 1/T 41724/H [ 477 …"}}
                char temp38_1 = *(cs + ecx_2);
                c_5 = temp38_1 < *ebx_3[1];
                p_2 = /* p_2 = unimplemented  {cmp byte [cs:ecx], bh} */;
                a_2 = /* a_2 = unimplemented  {cmp byte [cs:ecx], bh} */;
                z_4 = temp38_1 == *ebx_3[1];
                s_4 = (temp38_1 - *ebx_3[1]) < 0;
                *esp_23;
                esp_29 = (esp_23 + 4);
            label_3e1:
                char temp0_66;
                temp0_66 = __das(eax_10, eflags_16);
                eax_10 = temp0_66;
                *(esp_29 - 4) = eax_10;
                edi_6 = *(esp_29 - 4);
                esi_24 = *esp_29;
                ebp_6 = *(esp_29 + 4);
                ebx_3 = *(esp_29 + 0xc);
                edx_3 = *(esp_29 + 0x10);  {  // {"7 0 obj\r<</Linearized 1/L 42027…"}}
                ecx_2 = *(esp_29 + 0x14);  {  // {"obj\r<</Linearized 1/L 42027/O 1…"}}
                eax_10 = *(esp_29 + 0x18);  {  // {"<</Linearized 1/L 42027/O 10/E 3…"}}
                esp_23 = (esp_29 + 0x1c);  {  // {"inearized 1/L 42027/O 10/E 37847…"}}
                
                if (!(c_5))
                {
                    esi_24 = __outsb(edx_3, *esi_24, esi_24, eflags_24);
                    
                    if (z_4)
                        goto label_409;
                    
                    z_7 = eax_10 == 0x52203020;
                    char temp0_67;
                    temp0_67 = __das((eax_10 ^ 0x52203020), eflags_24);
                    eax_10 = temp0_67;
                    goto label_3ef;
                }
                
                *eax_10 ^= esi_24;
                *eax_10 ^= *ebx_3[1];
                char temp0_76;
                temp0_76 = __das(eax_10, eflags_24);
                eax_10 = temp0_76;
            label_450:
                esi_24 -= 1;
                *ecx_2 &= *edx_3[1];
                char temp40_1 = *edi_6;
                *edi_6 ^= *ecx_2[1];
                *(esp_23 - 4) = esp_23;
                esp_23 -= 4;
                
                if ((temp40_1 ^ *ecx_2[1]) < 0)
                {
                    char temp0_77;
                    temp0_77 = __das(eax_10, eflags_24);
                    eax_10 = temp0_77;
                    z_7 = edi_6 == 1;
                    __bound_gprv_mema32(ebp_6, *(edx_3 + 0x53));  {  // {"9]>>\rendobj\r                  …"}}
                    
                    if (!(z_7))
                        goto label_4d8;
                    
                    __outsb(edx_3, *esi_24, esi_24, eflags_24);
                    trap(0xf4);  {  // {"066BC5A54A9D2698D347D6B79C>]/Ind…"}}
                }
                
                void* temp44_1 = ebp_6;
                ebp_6 += 1;
                
                if (temp44_1 > 0xffffffff)
                    eax_21 = (eax_10 - 0x6048e2a7);
                else
                {
                    *ecx_2[1] = *((esi_24 + (ebp_6 << 1)) + 0x3bb0f4cd);
                label_527:
                    *eax_10;
                    *eax_10 ^= 0x58;  {  // {"endobj\r                   \r\n1…"}}
                    *(esp_23 - 4) = es;
                    esp_23 -= 4;
                    *edx_3[1] = (*edx_3[1] - *edx_3[1]);
                    bool c_9 = /* bool c_9 = unimplemented  {sbb dh, dh} */;
                    *(esi_24 + 0x26) = ebp_6;  {  // {"1/L 42027/O 10/E 37847/N 1/T 417…"}}
                    eax_21 = (eax_10 - 0x6048e2a7);
                }
            }
            
            if ((eax_21 & 0x7a) >= 0)  {  // {"bj\r<</DecodeParms<</Columns 4/P…"}}
            {
                *0x23758457;
                *esp_23;
                /* undefined */;
            }
            
            *esi_24;
            esi_24 += 1;
            __outsb(edx_3, *esi_24, esi_24, eflags_24);
            trap(0xf4);  {  // {"066BC5A54A9D2698D347D6B79C>]/Ind…"}}
        }
        
        esp_20[1];
        esp_20[2];
        int16_t ebx_4 = esp_20[4];
        edx = esp_20[5];
        ecx = esp_20[6];
        void* eax_11 = esp_20[7];
        int32_t* edi_8;
        int32_t temp0_32;
        temp0_32 = __insd(*esp_20, edx, eflags_16);
        *edi_8 = temp0_32;
        result = (eax_11 | 0x4c1b40a);
        *ecx[1] &= *ebx_4[1];
        *result;
        *(fsbase + (edx - 0x5bee7d6f)) = (RRCD(*(fsbase + (edx - 0x5bee7d6f)), ecx, false));
    }
    *result s>>= 1;
    *result;
    return result;
}

int32_t __convention("regparm") sub_a281(int32_t arg1, void* arg2, int32_t arg3, int32_t* arg4 @ edi, int32_t arg5, int32_t arg6, int32_t arg7, int32_t arg8, void* arg9)
{
    void* eax_1;
    int32_t ebx;
    bool s;
    bool o;
    
    if (s == o)
    {
        ebx = arg6;
        eax_1 = arg9;
    }
    else
    {
        eax_1 = (arg2 - 0x6e343173);
        
        if (arg2 >= 0x6e343173)
            breakpoint();
        
        *arg4 = eax_1;
        ebx = 0x61;  {  // {"                 \r\n16 0 obj\r<…"}}
    }
    
    *(ebx + 0x7160c513);
    *ebx[1] += *(eax_1 - 0x5375b398);
    /* undefined */;
}

int32_t __convention("regparm") sub_a2ac(int16_t arg1, uint64_t* arg2)
{
    int32_t edi;
    int16_t ds;
    edi = __lds_gprz_memp(*arg2);
    int16_t var_4 = &__return_addr;
    return (arg2 | 0xb8);  {  // {"ter/FlateDecode/ID[<6F4074632F7B…"}}
}

void __convention("fastcall") sub_a2b8(char* arg1, void* arg2, uint16_t* arg3 @ esi) __noreturn
{
    bool c;
    *arg1 = (*arg1 + 0x23);  {  // {"ed 1/L 42027/O 10/E 37847/N 1/T …"}}
    int32_t temp1 = *arg1;
    *arg1 -= arg3;
    
    if ((temp1 + -(arg3)))
    {
        *0xa0e078cb = *__return_addr;
        arg3 = (*(arg2 - 0x3e) * 0xd47f8e4d);  {  // {" 1/T 41724/H [ 477 159]>>\rendob…"}}
    }
    
    int32_t eax;
    int16_t edx;
    eax = 0xd49cb9c9();
    __int1();
    int32_t eflags;
    __outsb(edx, *arg3, arg3, eflags);
    int32_t ebx;
    ebx = 0x40;  {  // {"/T 41724/H [ 477 159]>>\rendobj\r…"}}
    breakpoint();
}

