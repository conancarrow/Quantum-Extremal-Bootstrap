(* ::Package:: *)

ClearAll[comm,op]
(*SetAttributes[op,Flat];*)
op[z___,a_*b_,y___]/;FreeQ[a,x|p]:=a op[z,b,y];
op[a_/;FreeQ[HoldPattern[a],x|p]&&a!=1]:=a op[1];
(*op[z___,a_/;FreeQ[a,x]&&FreeQ[a,p],y___]:=a op[z,y];*)
op[z__,a_/;FreeQ[a,x]&&FreeQ[a,p],y___]:=a op[z,y];
op[z___,a_/;FreeQ[a,x]&&FreeQ[a,p],y__]:=a op[z,y];
op/:op[1]^n_=op[1];
Format[op[1]]:=\[DoubleStruckOne];
op/:op[1]op[x__]:=op[x];
op[z___,a_+b_,y___]:= op[z,a,y]+op[z,b,y];
op[z___,HoldPattern[a_/;MatchQ[a,x|x^_]],HoldPattern[b_/;MatchQ[b,x|x^_]],y___]:=op[z,x^(Exponent[a,x]+Exponent[b,x]),y];
op[z___,HoldPattern[a_/;MatchQ[a,p|p^_]],HoldPattern[b_/;MatchQ[b,p|p^_]],y___]:=op[z,p^(Exponent[a,p]+Exponent[b,p]),y];
op[z___,HoldPattern[op[a__]],y___]:=op[z,a,y];

op[z___,
HoldPattern[a_/;MatchQ[a,p|p^_]],
HoldPattern[b_/;MatchQ[b,x|x^_]],
y___]:=op[z,(op[b,a]+comm[op[a],op[b]]),y];

comm[a_,a_]=0; 
comm[a_,b_/;FreeQ[b,x|p]]=0;
comm[a_/;FreeQ[a,x|p],b_]=0; 
comm[op[p],op[x]]:=-I op[1];
comm[op[x],op[p]]:=I op[1];
comm[a_+b_,y_]:=(
(*Print["[a+b,y]: ",comm[a,y]+comm[b,y]//HoldForm];*)
comm[a,y]+comm[b,y]
);
comm[HoldPattern[a_*b_/;FreeQ[a,x|p]],c_]:=(
(*Print["[a*b,c]: ",a comm[b,c]//HoldForm];*)
a comm[b,c]
);
comm[y_,a_+b_]:=( 
(*Print["[y,a+b]: ",comm[y,a]+comm[y,b]//HoldForm];*)
comm[y,a]+comm[y,b]
);
comm[c_,a_*b_/;FreeQ[a,x|p]]:=( 
(*Print["[c,ab]: ",a comm[c,b]//HoldForm];*)
a comm[c,b]
);
comm[HoldPattern[op[a__,b__]],c_]:=( 
(*Print["[ab,c]: ",
op[op[a], comm[op[b],c]]+op[ comm[op[a],c],op[b]]//HoldForm
];*)
op[op[a], comm[op[b],op[c]]]+op[ comm[op[a],op[c]],op[b]]
);
comm[a_,HoldPattern[op[b__,c__]]]:=( 
(*Print[
"[a,[b,c]]: ",
op[ comm[a,op[b]],op[c]]+op[op[b],comm[a,op[c]]]//HoldForm];*)
op[ comm[op[a],op[b]],op[c]]+op[op[b],comm[op[a],op[c]]]
);
comm[HoldPattern[op[x^m_]]/;m<0,c_]:=( 
(*Print[comm[w^m,c]=op[w, comm[w^(m-1),c]]+op[ comm[w,c],w^(m-1)]//HoldForm];*)
comm[op[x^m],op[c]]=op[x^-1,comm[op[x^(m+1)],op[c]]]-op[x^-1,comm[op[x],op[c]],x^m]
);
comm[a_,HoldPattern[op[x^m_]]/;m<0]:=( 
(*Print[comm[a,w^m]=op[ comm[a,w],w^(m-1)]+op[w,comm[a,w^(m-1)]]//HoldForm];*)
comm[op[a],op[x^m]]=op[comm[op[a],op[x^(m+1)]],x^-1]-op[x^m,comm[op[a],op[x]],x^-1]
);
comm[a_,HoldPattern[op[w_^m_]]]:=(
(*Print[comm[a,w^m]=op[ comm[a,w],w^(m-1)]+op[w,comm[a,w^(m-1)]]//HoldForm];*)
comm[op[a],op[w^m]]=op[ comm[op[a],op[w]],w^(m-1)]+op[w,comm[op[a],op[w^(m-1)]]]
);
comm[HoldPattern[op[w_^m_]],c_]:=(
(*Print[comm[w^m,c]=op[w, comm[w^(m-1),c]]+op[ comm[w,c],w^(m-1)]//HoldForm];*)
comm[op[w^m],op[c]]=op[w, comm[op[w^(m-1)],op[c]]]+op[ comm[op[w],op[c]],w^(m-1)]
);

