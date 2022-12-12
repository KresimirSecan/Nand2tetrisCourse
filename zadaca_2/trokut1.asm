
//prava stranica
@128
D = A
@n
M = D;
@i
M = 0;
@18439
D = A
@scr
M = D
// for (int i = 0; i < n; ++i)
(LOOP_START)
    // zaustavi petlju ako i >= n (i - n >= 0)
    @n
    D = M;
    @i
    D = M - D;
    @LOOP_END
    D; JGE
    // ---------------
    @scr   //obojaj adresu  na screenu
    A=M
    M=1

    @32  //pomakni na iducu tocku screen 
    D=A;
    @scr
    M=M+D;
    // ---------------
    @i
    M = M + 1;
    @LOOP_START
    0; JMP
(LOOP_END)


//donja stranica
@i
M=0;
@8
D = A
@n
M = D;

(LOOP_START2)
    // zaustavi petlju ako i >= n (i - n >= 0)
    @n
    D = M;
    @i
    D = M - D;
    @LOOP_END2
    D; JGE
    // ---------------
    @scr
    A = M
    M = -1    
    
    @scr
    M=M+1;
    // ---------------
    @i
    M = M + 1;
    @LOOP_START2
    0; JMP
(LOOP_END2)



//HIPOTENUZA
@i
M=0;
@8
D = A
@n
M = D;
@18439
D = A
@scr
M= D
@br
M=0
@dupler
M=1
(LOOP_START4)
    // zaustavi petlju ako i >= n (i - n >= 0)
    @n
    D = M;
    @i
    D = M - D;
    @END
    D; JGE
    // ---------------
    
    @dupler
    D=M;
    @scr
    A=M;
    M=M|D;

    @32
    D=A;
    @scr
    M=M+D;

    @i
    D=M;
    @PRVI
    D ; JEQ
    @OSTALI
    D ; JNE
  
    (DALJE)
    @br
    D=M-D
    @RESETBR
    D;JEQ
    @DUPLAJBR
    D;JLT
    
    (NASTAVI)
    @br
    M=M+1
    // ---------------
    @LOOP_START4
    0; JMP


(RESETBR)
@br
M=0
@dupler
M=1
@i
M = M + 1;
@scr
M=M+1;
@NASTAVI
0;JMP

(DUPLAJBR)
@dupler
D=M;
M=M+D;
@NASTAVI
0;JMP

(PRVI)
@15
D=A;
@DALJE
0; JMP

(OSTALI)
@16
D=A;
@DALJE
0; JMP

(END)
@END
0;JMP