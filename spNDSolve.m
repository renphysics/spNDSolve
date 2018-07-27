(* ::Package:: *)

(*
spNDSolve v0.1, by Jie Ren, 2018/7/28
A Mathematica package for solving PDEs by the pseudospectral method
*)


bryIndex::usage = "bryIndex[m,n]";
bryLinearize::usage = "bryLinearize[{flist,reflist},{{bryind1,brylist1},{bryind2,brylist2}}]";
changeVariable::usage = "changeVariable[expr_, hlist_, varlist_, trans_, invtrans_, simp_:Identity], hlist is function heads, varlist is old variables, trans is old variables expressed in terms of new variables";
cheb::usage = "See the detailed documentation";
domainCompose::usage = "lhs1\[CirclePlus]lhs2, and impose interface boundary conditions";
eqLinearize::usage = "eqLinearize[{flist,reflist},{eqlist,\"eqlist\",\"mat\"}] or eqLinearize[{flist,reflist},{eqlist,\"eqlist\",\"mat\",True,\"eqlistmat\"}]";
spNDSolve::usage="spNDSolve[{x_, y_}, {fx_, fy_}, {nxGrid0_, nyGrid0_}, {par___}, s_String:\"\", OptionsPattern[]]";
spNIntegrate::usage = "spNIntegrate[x, fx, nxGrid0, expr, \"s\", rules]. It calls cheb[x, fx, nxGrid0, s, rules] and produces global variables \"lhs\" and \"rhs\" with surfix \"s\". e.g., spNIntegrate[x, linearMap[{1, 2}], 20, Sin[x], \"s\"]\[LeftDoubleBracket]-1\[RightDoubleBracket] does the work of NIntegrate[Sin[x], {x, 1, 2}]";


CircleTimes=KroneckerProduct;


CirclePlus[x__]:=ArrayFlatten@ReleaseHold@DiagonalMatrix[Hold/@{x}];


Diamond[x__]:=toHeldExpression@StringJoin[Sequence@@toString[{x}]];
SetAttributes[Diamond,{HoldAll,Listable}];


DotEqual[a_HoldForm,b_]:=(a/.hold[lft_]:>hold[lft=b])//ReleaseHold;  (*not a_hold*)
DotEqual[a_List,b_List]:=MapThread[DotEqual,{a,b}];


Vee[x__]:=ToExpression[StringJoin[Sequence@@toString[{x}]]];
Attributes[Vee]={HoldAll,Listable};


addTo[a_List,b_List]:=MapThread[AddTo,{a,b}];  (*a=Unevaluated/@lista*)


arcTanh[x_]:=ArcTanh[round[x]];  (*arcTanh[-1.]=-\[Infinity], arcTanh[0.]=0*)


arrayDrop[m_,ind_]:=m[[##]]&@@(Complement[Range@#,Flatten[{ind}]]&/@Dimensions[m]);  (*faster than Module[{lis=List/@Flatten[{ind}]},Delete[Delete[m,lis]\[Transpose],lis]\[Transpose]]*)


bryIndex[m_Integer,{n_Integer},s_String:""]:=Which[dimPDE===1,
Which[m==1,{(n-1) dimGrid\[Vee]s+1},  (*xCheb=-1*)
m==2,{n dimGrid\[Vee]s}  (*xCheb=1*)],
dimPDE===2,
Which[m==1,Flatten[(n-1) dimGrid\[Vee]s+Table[i,{i,1,nyGrid\[Vee]s+1}]],  (*xCheb=-1*)
m==2,Flatten[(n-1) dimGrid\[Vee]s+Table[i,{i,nxGrid\[Vee]s(nyGrid\[Vee]s+1)+1,nxGrid\[Vee]s(nyGrid\[Vee]s+1)+nyGrid\[Vee]s+1}]],  (*xCheb=1*)
m==3,Flatten[(n-1) dimGrid\[Vee]s+Table[i(nyGrid\[Vee]s+1)+1,{i,0,nxGrid\[Vee]s}]],  (*yCheb=-1*)
m==4,Flatten[(n-1) dimGrid\[Vee]s+Table[i(nyGrid\[Vee]s+1)+nyGrid\[Vee]s+1,{i,0,nxGrid\[Vee]s}]],  (*yCheb=1*)
m==13,{(n-1) dimGrid\[Vee]s+1},  (*xCheb=-1, yCheb=-1*)
m==14,{(n-1) dimGrid\[Vee]s+nyGrid\[Vee]s+1},  (*xCheb=1, yCheb=1*)
m==23,{(n-1) dimGrid\[Vee]s+nxGrid\[Vee]s(nyGrid\[Vee]s+1)+1},  (*xCheb=1, yCheb=-1*)
m==24,{n dimGrid\[Vee]s}  (*xCheb=1, yCheb=1*)]];
bryIndex[m_Integer,{n__Integer},s_String:""]:=bryIndex[m,{#},s]&/@{n}//Flatten;
bryIndex[m_List,{n__Integer},s_String:""]:=bryIndex[#,{n},s]&/@m;
bryIndex[m_Integer,nEq_Integer,s_String:""]:=Table[bryIndex[m,{n},s],{n,1,nEq}]//Flatten;
bryIndex[m_List,nEq_Integer,s_String:""]:=bryIndex[#,nEq,s]&/@m;
bryIndex[m_,s_String:""]:=bryIndex[m,nEq\[Vee]s,s];
bryIndex[m_,nEq_Integer,"c",s_String:""]:=Complement[Range[dimGrid\[Vee]s nEq],Flatten@bryIndex[m,nEq,s]];


bryLinearize[{flist_,reflist___},bryprerepl_,s_String:""]:=Module[{bryprereplh,strtemp,listtemp,mattemp,brylinearize},
bryprereplh=hold[bryprerepl];
strtemp=Map[toString,bryprereplh,{3}]//release;
listtemp=strtemp[[;;,2]];
mattemp=StringReplace[listtemp,"list"->"mat"];
bryrepl\[Diamond]s\[DotEqual]unmap@toHeldExpression[Join[strtemp\[Transpose],{mattemp}]\[Transpose]];
brylinearize=Join[{ToExpression[listtemp]},{listtemp},{mattemp}]\[Transpose];
eqLinearize[{flist,reflist},brylinearize,s];];
SetAttributes[bryLinearize,HoldAll];


bryReplace[bryind_?VectorQ,brylist_,brymat_,s_String:""]:={lhs\[Diamond]s[[bryind]]\[DotEqual]ArrayFlatten[brymat][[bryind]],rhs\[Diamond]s[[bryind]]\[DotEqual]-Flatten[brylist][[bryind]]};
bryReplace[x__List,s_String:""]:=bryReplace[Sequence@@#,s]&/@{x};


calcDeriv[f_[x_?AtomQ]]:={f\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f};
calcDeriv[f_[x_?AtomQ,y_?AtomQ]]:={f\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]y\[Diamond]"."\[Diamond]f};
calcDeriv[f_[x_?AtomQ,y_?AtomQ,z_?AtomQ]]:={f\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]z\[Diamond]"="\[Diamond]"d"\[Diamond]z\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]z\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]z\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]z\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]z\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]z\[Diamond]z\[Diamond]"="\[Diamond]"d"\[Diamond]z\[Diamond]z\[Diamond]"."\[Diamond]f};
calcDeriv[flist_List]:=calcDeriv[#//Flatten]&/@flist//Flatten;


Options[calcInterp]={derivQ->False};
calcInterp[f_[x_?AtomQ],suf_String:"f",opt:OptionsPattern[]]:=Module[{lft,rt},
lft={f,f\[Diamond]x,f\[Diamond]x\[Diamond]x}//ReleaseHold;
rt={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]x\[Diamond]x}//ReleaseHold;
If[OptionValue[derivQ]==True,MapThread[hold[#1=#2[x]]&,{lft,rt}],MapThread[hold[#1=#2[x]]&,{{lft[[1]]},{rt[[1]]}}]]];
calcInterp[f_[x_?AtomQ,y_?AtomQ],suf_String:"f",opt:OptionsPattern[]]:=Module[{lft,rt},
lft={f,f\[Diamond]x,f\[Diamond]y,f\[Diamond]x\[Diamond]y,f\[Diamond]x\[Diamond]x,f\[Diamond]y\[Diamond]y}//ReleaseHold;
rt={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]x,f\[Diamond]suf\[Diamond]y\[Diamond]y}//ReleaseHold;
If[OptionValue[derivQ]==True,MapThread[hold[#1=#2[x,y]]&,{lft,rt}],MapThread[hold[#1=#2[x,y]]&,{{lft[[1]]},{rt[[1]]}}]]];
calcInterp[flist_List,suf_String:"f",opt:OptionsPattern[]]:=calcInterp[#//Flatten,suf,opt]&/@flist//Flatten;


changeOptions[f_,a_->b_]:=If[MemberQ[f,a->x_],f/.(a->x_)->(a->b),Head[f][Sequence@@f,a->b]];
changeOptions[f_,rule__Rule]:=Fold[changeOptions,f,{rule}];


changeVariable[expr_,hlist_,varlist_,trans_,invtrans_,simp_:Identity]:=Module[{fsubs,varsubs},  (*trans=var[newvar]*)
fsubs=Map[#->Function[Evaluate[varlist],Evaluate[#[Sequence@@invtrans]]]&,hlist];
varsubs=MapThread[Rule,{varlist,trans}];
expr/.fsubs/.varsubs//simp];


Options[cheb]={minPrec->0,"D"->False};
cheb[x_,fx_Function,nxGrid0_,s_String:"",OptionsPattern[]]:=Block[{xtemp,fdx,fdxCheb,fdxCheb2,ind1,ind2,ind1rep,ind2rep},
dimPDE=1;
{nxGrid\[Diamond]s,xCheb\[Diamond]s,dxCheb\[Diamond]s}\[DotEqual]chebx[nxGrid0,OptionValue[minPrec]];
dimGrid\[Diamond]s\[DotEqual](nxGrid\[Vee]s+1);
If[AtomQ[nxGrid0]==False&&nxGrid0[[-1]]==="periodic",xPeriod\[Diamond]s\[DotEqual]fx[2\[Pi]];,Clear[Evaluate["xPeriod"<>s]];];
x=fx[xCheb\[Vee]s]//Quiet;

ind1=bryIndex[1,1,s];  (*replace boundaries "1" & "2"*)
ind2=bryIndex[2,1,s];
ind1rep=ind1+1;
ind2rep=ind2-1;
x\[Diamond]"aux1"\[Diamond]"="\[Diamond]x\[Diamond]"aux2"\[Diamond]"="\[Diamond]x\[Diamond]"aux12"\[Diamond]"="\[Diamond]x//release;
x\[Diamond]"aux1"\[Diamond]"\[LeftDoubleBracket]ind1\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind1rep\[RightDoubleBracket]"//release;
x\[Diamond]"aux2"\[Diamond]"\[LeftDoubleBracket]ind2\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind2rep\[RightDoubleBracket]"//release;
x\[Diamond]"aux12"\[Diamond]"\[LeftDoubleBracket]ind1\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind1rep\[RightDoubleBracket]"//release;
x\[Diamond]"aux12"\[Diamond]"\[LeftDoubleBracket]ind2\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind2rep\[RightDoubleBracket]"//release;

fdx[xtemp_]=1/fx'[xtemp]//Simplify;
fdxCheb=fdx[xCheb\[Vee]s]dxCheb\[Vee]s; fdxCheb2=fdxCheb.fdxCheb;
{"d"\[Diamond]x\[Diamond]"="\[Diamond]fdxCheb,"d"\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond]fdxCheb2}//release;
If[OptionValue["D"]=!=False,{"d"\[Diamond]x,"d"\[Diamond]x\[Diamond]x}\[DotEqual](arrayDrop[#,bryIndex[OptionValue["D"],1]]&/@{"d"\[Vee]x,"d"\[Vee]x\[Vee]x})]; (*homogeneous Dirichlet boundary conditions*)
id\[Diamond]s\[DotEqual]IdentityMatrix[nxGrid\[Vee]s+1];
zero\[Diamond]s\[DotEqual]0id\[Vee]s;
one\[Diamond]s\[DotEqual]Table[1,{dimGrid\[Vee]s}];];
cheb[x_,nxGrid0_,s_String:"",opt:OptionsPattern[]]:=cheb[x,#&,nxGrid0,s,opt]; (*downvalue must be after cheb[{x_, y_}, {nxGrid0_, nyGrid0_}, ...]*)

cheb[{x_,y_},{fx_Function,fy_Function},{nxGrid0_,nyGrid0_},s_String:"",OptionsPattern[]]:=Block[{xtemp,ytemp,fdx,fdy,fdxCheb,fdxCheb2,fdyCheb,fdyCheb2,idx,idy,ind1,ind2,ind1rep,ind2rep},
dimPDE=2;
{nxGrid\[Diamond]s,xCheb\[Diamond]s,dxCheb\[Diamond]s}\[DotEqual]chebx[nxGrid0,OptionValue[minPrec]];
{nyGrid\[Diamond]s,yCheb\[Diamond]s,dyCheb\[Diamond]s}\[DotEqual]chebx[nyGrid0,OptionValue[minPrec]];
dimGrid\[Diamond]s\[DotEqual](nxGrid\[Vee]s+1)(nyGrid\[Vee]s+1);
If[AtomQ[nxGrid0]==False&&nxGrid0[[-1]]==="periodic",xPeriod\[Diamond]s\[DotEqual]fx[2\[Pi]];,Clear[Evaluate["xPeriod"<>s]];];
If[AtomQ[nyGrid0]==False&&nyGrid0[[-1]]==="periodic",yPeriod\[Diamond]s\[DotEqual]fy[2\[Pi]];,Clear[Evaluate["yPeriod"<>s]];];
idx=IdentityMatrix[nxGrid\[Vee]s+1];
idy=IdentityMatrix[nyGrid\[Vee]s+1];
x=Flatten[fx[xCheb\[Vee]s]\[CircleTimes]Table[1,{nyGrid\[Vee]s+1}]]//Quiet;
y=Flatten[Table[1,{nxGrid\[Vee]s+1}]\[CircleTimes]fy[yCheb\[Vee]s]]//Quiet;

ind1=bryIndex[1,1,s];  (*replace boundaries "1" & "2"*)
ind2=bryIndex[2,1,s];
ind1rep=ind1+nyGrid\[Vee]s+1;
ind2rep=ind2-nyGrid\[Vee]s-1;
x\[Diamond]"aux1"\[Diamond]"="\[Diamond]x\[Diamond]"aux2"\[Diamond]"="\[Diamond]x\[Diamond]"aux12"\[Diamond]"="\[Diamond]x//release;
x\[Diamond]"aux1"\[Diamond]"\[LeftDoubleBracket]ind1\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind1rep\[RightDoubleBracket]"//release;
x\[Diamond]"aux2"\[Diamond]"\[LeftDoubleBracket]ind2\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind2rep\[RightDoubleBracket]"//release;
x\[Diamond]"aux12"\[Diamond]"\[LeftDoubleBracket]ind1\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind1rep\[RightDoubleBracket]"//release;
x\[Diamond]"aux12"\[Diamond]"\[LeftDoubleBracket]ind2\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind2rep\[RightDoubleBracket]"//release;

ind1=bryIndex[3,1,s];  (*replace boundaries "3" & "4"*)
ind2=bryIndex[4,1,s];
ind1rep=ind1+1;
ind2rep=ind2-1;
y\[Diamond]"aux1"\[Diamond]"="\[Diamond]y\[Diamond]"aux2"\[Diamond]"="\[Diamond]y\[Diamond]"aux12"\[Diamond]"="\[Diamond]y//release;
y\[Diamond]"aux1"\[Diamond]"\[LeftDoubleBracket]ind1\[RightDoubleBracket]"\[Diamond]"="\[Diamond]y\[Diamond]"\[LeftDoubleBracket]ind1rep\[RightDoubleBracket]"//release;
y\[Diamond]"aux2"\[Diamond]"\[LeftDoubleBracket]ind2\[RightDoubleBracket]"\[Diamond]"="\[Diamond]y\[Diamond]"\[LeftDoubleBracket]ind2rep\[RightDoubleBracket]"//release;
y\[Diamond]"aux12"\[Diamond]"\[LeftDoubleBracket]ind1\[RightDoubleBracket]"\[Diamond]"="\[Diamond]y\[Diamond]"\[LeftDoubleBracket]ind1rep\[RightDoubleBracket]"//release;
y\[Diamond]"aux12"\[Diamond]"\[LeftDoubleBracket]ind2\[RightDoubleBracket]"\[Diamond]"="\[Diamond]y\[Diamond]"\[LeftDoubleBracket]ind2rep\[RightDoubleBracket]"//release;

fdx[xtemp_]=1/fx'[xtemp]//Simplify;
fdy[ytemp_]=1/fy'[ytemp]//Simplify;
fdxCheb=fdx[xCheb\[Vee]s]dxCheb\[Vee]s; fdxCheb2=fdxCheb.fdxCheb;
fdyCheb=fdy[yCheb\[Vee]s]dyCheb\[Vee]s; fdyCheb2=fdyCheb.fdyCheb;
{"d"\[Diamond]x\[Diamond]"="\[Diamond](fdxCheb\[CircleTimes]idy),"d"\[Diamond]y\[Diamond]"="\[Diamond](idx\[CircleTimes]fdyCheb),"d"\[Diamond]x\[Diamond]y\[Diamond]"="\[Diamond](fdxCheb\[CircleTimes]fdyCheb),"d"\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond](fdxCheb2\[CircleTimes]idy),"d"\[Diamond]y\[Diamond]y\[Diamond]"="\[Diamond](idx\[CircleTimes]fdyCheb2)}//ReleaseHold;
If[OptionValue["D"]=!=False,{"d"\[Diamond]x,"d"\[Diamond]y,"d"\[Diamond]x\[Diamond]y,"d"\[Diamond]x\[Diamond]x,"d"\[Diamond]y\[Diamond]y}\[DotEqual](arrayDrop[#,bryIndex[OptionValue["D"],1]]&/@{"d"\[Vee]x,"d"\[Vee]y,"d"\[Vee]x\[Vee]y,"d"\[Vee]x\[Vee]x,"d"\[Vee]y\[Vee]y})];  (*homogeneous Dirichlet boundary conditions*)
id\[Diamond]s\[DotEqual]idx\[CircleTimes]idy;
zero\[Diamond]s\[DotEqual]0id\[Vee]s;
one\[Diamond]s\[DotEqual]Table[1,{dimGrid\[Vee]s}];];
cheb[{x_,y_},{nxGrid0_,nyGrid0_},s_String:"",opt:OptionsPattern[]]:=cheb[{x,y},{#&,#&},{nxGrid0,nyGrid0},s,opt];

cheb[{x_,y_,z_},{fx_Function,fy_Function,fz_Function},{nxGrid0_,nyGrid0_,nzGrid0_},s_String:"",OptionsPattern[]]:=Block[{xtemp,ytemp,ztemp,fdx,fdy,fdz,fdxCheb,fdxCheb2,fdyCheb,fdyCheb2,fdzCheb,fdzCheb2,idx,idy,idz,ind1,ind2,ind1rep,ind2rep},
dimPDE=3;
{nxGrid\[Diamond]s,xCheb\[Diamond]s,dxCheb\[Diamond]s}\[DotEqual]chebx[nxGrid0,OptionValue[minPrec]];
{nyGrid\[Diamond]s,yCheb\[Diamond]s,dyCheb\[Diamond]s}\[DotEqual]chebx[nyGrid0,OptionValue[minPrec]];
{nzGrid\[Diamond]s,zCheb\[Diamond]s,dzCheb\[Diamond]s}\[DotEqual]chebx[nzGrid0,OptionValue[minPrec]];
dimGrid\[Diamond]s\[DotEqual](nxGrid\[Vee]s+1)(nyGrid\[Vee]s+1)(nzGrid\[Vee]s+1);
If[AtomQ[nxGrid0]==False&&nxGrid0[[-1]]==="periodic",xPeriod\[Diamond]s\[DotEqual]fx[2\[Pi]];,Clear[Evaluate["xPeriod"<>s]];];
If[AtomQ[nyGrid0]==False&&nyGrid0[[-1]]==="periodic",yPeriod\[Diamond]s\[DotEqual]fy[2\[Pi]];,Clear[Evaluate["yPeriod"<>s]];];
If[AtomQ[nzGrid0]==False&&nzGrid0[[-1]]==="periodic",zPeriod\[Diamond]s\[DotEqual]fz[2\[Pi]];,Clear[Evaluate["zPeriod"<>s]];];
idx=IdentityMatrix[nxGrid\[Vee]s+1];
idy=IdentityMatrix[nyGrid\[Vee]s+1];
idz=IdentityMatrix[nzGrid\[Vee]s+1];
x=Flatten[fx[xCheb\[Vee]s]\[CircleTimes]Table[1,{nyGrid\[Vee]s+1}]]\[CircleTimes]Table[1,{nzGrid\[Vee]s+1}]//Quiet;
y=Flatten[Table[1,{nxGrid\[Vee]s+1}]\[CircleTimes]fy[yCheb\[Vee]s]\[CircleTimes]Table[1,{nzGrid\[Vee]s+1}]]//Quiet;
z=Flatten[Table[1,{nxGrid\[Vee]s+1}]\[CircleTimes]Table[1,{nyGrid\[Vee]s+1}]\[CircleTimes]fz[zCheb\[Vee]s]]//Quiet;

fdx[xtemp_]=1/fx'[xtemp]//Simplify;
fdy[ytemp_]=1/fy'[ytemp]//Simplify;
fdz[ztemp_]=1/fz'[ztemp]//Simplify;
fdxCheb=fdx[xCheb\[Vee]s]dxCheb\[Vee]s; fdxCheb2=fdxCheb.fdxCheb;
fdyCheb=fdy[yCheb\[Vee]s]dyCheb\[Vee]s; fdyCheb2=fdyCheb.fdyCheb;
fdzCheb=fdz[zCheb\[Vee]s]dzCheb\[Vee]s; fdzCheb2=fdzCheb.fdzCheb;
{"d"\[Diamond]x\[Diamond]"="\[Diamond](fdxCheb\[CircleTimes]idy\[CircleTimes]idz),"d"\[Diamond]y\[Diamond]"="\[Diamond](idx\[CircleTimes]fdyCheb\[CircleTimes]idz),"d"\[Diamond]z\[Diamond]"="\[Diamond](idx\[CircleTimes]idy\[CircleTimes]fdzCheb),"d"\[Diamond]x\[Diamond]y\[Diamond]"="\[Diamond](fdxCheb\[CircleTimes]fdyCheb\[CircleTimes]idz),"d"\[Diamond]x\[Diamond]z\[Diamond]"="\[Diamond](fdxCheb\[CircleTimes]idy\[CircleTimes]fdzCheb),"d"\[Diamond]y\[Diamond]z\[Diamond]"="\[Diamond](idx\[CircleTimes]fdyCheb\[CircleTimes]fdzCheb),"d"\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond](fdxCheb2\[CircleTimes]idy\[CircleTimes]idz),"d"\[Diamond]y\[Diamond]y\[Diamond]"="\[Diamond](idx\[CircleTimes]fdyCheb2\[CircleTimes]idz),"d"\[Diamond]z\[Diamond]z\[Diamond]"="\[Diamond](idx\[CircleTimes]idy\[CircleTimes]fdzCheb2)}//ReleaseHold;
id\[Diamond]s\[DotEqual]idx\[CircleTimes]idy\[CircleTimes]idz;
zero\[Diamond]s\[DotEqual]0id\[Vee]s;
one\[Diamond]s\[DotEqual]Table[1,{dimGrid\[Vee]s}];];
cheb[{x_,y_,z_},{nxGrid0_,nyGrid0_,nzGrid0_},s_String:"",opt:OptionsPattern[]]:=cheb[{x,y,z},{#&,#&,#&},{nxGrid0,nyGrid0,nzGrid0},s,opt];
SetAttributes[cheb,HoldFirst];


chebx[nxGrid0_,minPrec_:0]:=Module[{nxGrid,xCheb,dxCheb},
If[minPrec!=0,
prec=$MinPrecision=minPrec;,
$MinPrecision=0;
prec=MachinePrecision;];
If[AtomQ[nxGrid0]==True,  (*x pseudospectral*)
nxGrid=nxGrid0;
xCheb=-N[Table[Cos[(j \[Pi])/nxGrid],{j,0,nxGrid}],prec];
If[$useNDSolve===True,
dxCheb=NDSolve`FiniteDifferenceDerivative[1,xCheb,DifferenceOrder->"Pseudospectral"]["DifferentiationMatrix"]//Normal;,
dxCheb=N[Table[If[i!=j,(-1)^(i+j)/(xCheb[[i]]-xCheb[[j]]) If[i==1||i==nxGrid+1,2,1]/If[j==1||j==nxGrid+1,2,1],0],{i,nxGrid+1},{j,nxGrid+1}],prec];
dxCheb=dxCheb-DiagonalMatrix[Plus@@@dxCheb];];,  (*Negative sum trick*)

nxGrid=nxGrid0[[1]];  (*x finite difference, nxGrid0={grid size, order, grid type}*)
Which[nxGrid0[[-1]]==="cheb",  (*Cheb grid*)
xCheb=-N[Table[Cos[(j \[Pi])/nxGrid],{j,0,nxGrid}],prec];
dxCheb=NDSolve`FiniteDifferenceDerivative[1,xCheb,DifferenceOrder->nxGrid0[[2]]]["DifferentiationMatrix"]//Normal;,

nxGrid0[[-1]]==="uniform"||Head[nxGrid0[[-1]]]===Integer,  (*uniform grid, default*)
xCheb=-N[Table[(nxGrid-2j)/nxGrid,{j,0,nxGrid}],prec];
dxCheb=NDSolve`FiniteDifferenceDerivative[1,xCheb,DifferenceOrder->nxGrid0[[2]]]["DifferentiationMatrix"]//Normal;,

nxGrid0[[-1]]==="periodic",  (*periodic*)
nxGrid+=1;
xCheb=N[Table[(2\[Pi] j)/nxGrid,{j,0,nxGrid}],prec];
If[$useNDSolve===True,
dxCheb=NDSolve`FiniteDifferenceDerivative[1,xCheb,PeriodicInterpolation->True,DifferenceOrder->"Pseudospectral"]["DifferentiationMatrix"]//Normal;,
dxCheb=N[Table[If[i!=j,(-1)^(i+j)/2 If[EvenQ[nxGrid],Cot,Csc][(xCheb[[i]]-xCheb[[j]])/2],0],{i,nxGrid},{j,nxGrid}],prec];
dxCheb=dxCheb-DiagonalMatrix[Plus@@@dxCheb];];  (*Negative sum trick*)
xCheb=xCheb[[1;;-2]]; nxGrid-=1;];];
{nxGrid,xCheb,dxCheb}];


clear[x_]:=(Clear[x];x);
SetAttributes[clear,HoldAll];


collect[eq_,vars_List,trans_:Simplify]:=Collect[eq/Coefficient[eq,vars[[1]]],vars,trans];


cond[mat_?MatrixQ]:=Divide@@Table[SingularValueList[mat,k,Tolerance->0][[1]],{k,{1,-1}}];  (*2-norm ondition number*)


continue[expr_,plists__List]:=Module[{lis,nlis,lismin,lismax,listab,i},  (*plists = {p1, p1min, p1max, dp1}, ..., {pn, pnmin, pnmax, dpn}*)
lis={plists};
nlis=Length[lis];
Do[If[Length[lis[[i]]]==2,AppendTo[lis[[i]],lis[[i,2]]]],{i,nlis}];  (*{p, pmin} \[Rule] {p, pmin, pmin}*)
lismin=Part[#,{1,2,2}]&/@lis;  (*lismin = {p, pmin, pmin}*)
lismax=Part[#,{1,3,3}]&/@lis;  (*lismax = {p, pmax, pmax}*)
Do[If[Length[lis[[i]]]==4,lis[[i,3]]-=lis[[i,4]],lis[[i,3]]-=1],{i,Length[lis]-1}];  (*{p, pmin, pmax, dp} \[Rule] {p, pmin, pmax-dp, dp}, {p, pmin, pmax} \[Rule] {p, pmin, pmax-1}*)
listab=Table[{Sequence@@lismax[[;;i-1]],lis[[i]],Sequence@@lismin[[i+1;;]]},{i,1,Length[lis]}];  (*e.g., {p1, p1max, p1max, dp1}, {p2, p2min, p2max-dp2, dp2}, {p3, p3min, p3min, dp3}*)
Flatten[Table[expr,Evaluate[Sequence@@#]]&/@listab,nlis]];  (*the last is for {p1, p1max, p1max}, ..., {pn, pnmax, pnmax}*)
SetAttributes[continue,HoldFirst];


deleteFactor[expr_Times,mem_]:=DeleteCases[expr,temp_/;FreeQ[temp,Alternatives@@mem,Heads->True],1];
deleteFactor[expr_,mem_]:=expr;
deleteFactor[expr_List,mem_]:=deleteFactor[#,mem]&/@expr;


deleteFactorSimplify[expr_,mem_,lev_:1]:=deleteFactor[If[lev==1,Simplify,FullSimplify]@Numerator@Together[expr],mem];


derivL[f_[x_?AtomQ]]:={f\[Diamond]x,f\[Diamond]x\[Diamond]x};
derivL[f_[x_?AtomQ,y_?AtomQ]]:={f\[Diamond]x,f\[Diamond]y,f\[Diamond]x\[Diamond]y,f\[Diamond]x\[Diamond]x,f\[Diamond]y\[Diamond]y};
derivL[flist_List]:=derivL[#//Flatten]&/@flist//Flatten;


derivR[f_[x_?AtomQ]]:={"d"\[Diamond]x\[Diamond]"."\[Diamond]f,"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f};
derivR[f_[x_?AtomQ,y_?AtomQ]]:={"d"\[Diamond]x\[Diamond]"."\[Diamond]f,"d"\[Diamond]y\[Diamond]"."\[Diamond]f,"d"\[Diamond]x\[Diamond]y\[Diamond]"."\[Diamond]f,"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f,"d"\[Diamond]y\[Diamond]y\[Diamond]"."\[Diamond]f};
derivR[flist_List]:=derivR[#//Flatten]&/@flist//Flatten;


deTurck:=(\[Xi]=contract[lower[Christoffel-\[CapitalGamma]bar,{1}],{2,3}];  (*need diffgeo.m*)
del\[Xi]=Symmetrize@Table[D[\[Xi],coord[[ii]]],{ii,1,dimen}]-Sum[Christoffel[[ii]]\[Xi][[ii]],{ii,1,dimen}];  (*del\[Xi]=symmetrize@covariant[\[Xi]]*)
\[Xi]2=contract[\[Xi]**\[Xi]]//noSimplify;)


dFunc[f_[x_?AtomQ]]:={f[x],f'[x],f''[x]};
dFunc[f_[x_?AtomQ,y_?AtomQ]]:={f[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]};
dFunc[f_[x_?AtomQ,y_?AtomQ,z_?AtomQ]]:={f[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]};
dFunc[fcn_List]:=dFunc[#]&/@fcn//Flatten;


diag[vec_?VectorQ]:=DiagonalMatrix[vec];
diag[mat_?MatrixQ]:=Module[{i},Table[mat[[i,i]],{i,Length[mat]}]];


domainCompose[s1_String,s2_String]:=Block[{nEq=nEq\[Vee]s1,dimGrid1=dimGrid\[Vee]s1,ind1,ind2,mat11,mat12,mat21,mat22},
{ind1,mat11,mat21}=itfrepl\[Vee]s1//release;
{ind2,mat12,mat22}=itfrepl\[Vee]s2//release;
lhs=(lhs\[Vee]s1)\[CirclePlus](lhs\[Vee]s2);
rhs=Join[rhs\[Vee]s1,rhs\[Vee]s2];
lhs[[ind1]]={{ArrayFlatten[mat11][[ind1]],-ArrayFlatten[mat12][[ind2]]}}//ArrayFlatten;
lhs[[ind2+nEq dimGrid1]]={{ArrayFlatten[mat21][[ind1]],-ArrayFlatten[mat22][[ind2]]}}//ArrayFlatten;
rhs[[ind1]]=0;
rhs[[ind2+nEq dimGrid1]]=0;];


dRule[f_[x_]->expr_]:={f[x]->expr,f'[x]->D[expr,x],f''[x]->D[expr,x,x]};
dRule[f_[x_,y_]->expr_]:={f[x,y]->expr,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,x],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,x,x],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,y,y]};
dRule[flist_List]:=dRule[#]&/@flist//Flatten;


drop[m_,parts__List]/;Length@{parts}<=ArrayDepth[m]:=m[[##]]&@@MapThread[Complement,{Range@Dimensions[m,Length@{parts}],{parts}}];


eqLinearize[{flist_List,reflist___List},{eqlist_List,eqname_String,matname_String,file_:False,eqlistmat_String:""},s_String:""]:=Module[{dim,x,y,sx,sy,eqtemp,mattemp},
If[prelinearize=!={{flist,reflist},s},preLinearize[{flist,reflist},s];];
eqtemp=eqlist//.replrule\[Vee]s;
If[eqtemp===eqlist,Print["Already replaced; Return"]; Return[];];  (*prevent being evaluated more than once*)
dim=Length[List@@flist[[1]]];
Which[dim==1,
x=Identity@@flist[[1]];
sx=ToString[x];
mattemp=Table[D[eqlist[[i]],D[flist[[j]],x,x]]ToExpression["d"<>sx<>sx]+D[eqlist[[i]],D[flist[[j]],x]]ToExpression["d"<>sx]+D[eqlist[[i]],flist[[j]]]ToExpression["id"<>s]+ToExpression["zero"<>s],{i,Length[eqlist]},{j,Length[flist]}]//.replrule\[Vee]s;,
dim==2,
{x,y}=List@@flist[[1]];
{sx,sy}=ToString/@{x,y};
mattemp=Table[D[eqlist[[i]],D[flist[[j]],x,x]]ToExpression["d"<>sx<>sx]+D[eqlist[[i]],D[flist[[j]],y,y]]ToExpression["d"<>sy<>sy]+D[eqlist[[i]],D[flist[[j]],x,y]]ToExpression["d"<>sx<>sy]+D[eqlist[[i]],D[flist[[j]],x]]ToExpression["d"<>sx]+D[eqlist[[i]],D[flist[[j]],y]]ToExpression["d"<>sy]+D[eqlist[[i]],flist[[j]]]ToExpression["id"<>s]+ToExpression["zero"<>s],{i,Length[eqlist]},{j,Length[flist]}]//.replrule\[Vee]s;];
{eqname\[Diamond]"="\[Diamond]eqtemp,matname\[Diamond]"="\[Diamond]mattemp}//ReleaseHold;
If[file==True,Put[eqtemp,eqname]; Put[mattemp,matname];];
If[eqlistmat!="",Put[optimize[{eqtemp,mattemp}],eqlistmat];];];
eqLinearize[{flist_List,reflist___List},{y__List},s_String:""]:=eqLinearize[{flist,reflist},#,s]&/@{y};


get[name__,rule___Rule]:=Module[{nam},  (*get[name1, name2, z \[Rule] aux12]*)
nam=List@@(Unevaluated/@Hold[name]);
set[nam,release["<<"\[Diamond]{name}]/.{rule}]];
SetAttributes[get,HoldAll];


hD:=HoldForm[D[##]]&;


hold=HoldForm;


insert[list_,val_,pos_]:=Join[val,list][[Ordering@Join[pos,Range@Length@list]]];


interp[x_][y1_,y2_]:=(1-x)/2 y1+(1+x)/2 y2;


interp[x_,y_,s_String:"",opt:OptionsPattern[]]:=Interpolation[{x,y}\[Transpose],opt];  (*function y[x]*)
interp[x_,y_,z_,s_String:"",opt:OptionsPattern[]]:=Module[{px,py,pz,xx,yy,zz,one},  (*function z[x, y]*)
If[(NumericQ[xPeriod\[Vee]s]||NumericQ[yPeriod\[Vee]s])=!=True,Interpolation[{{x,y}\[Transpose],z}\[Transpose],opt],
{px,py,pz}=Partition[#,nyGrid\[Vee]s+1]&/@{x,y,z};
If[NumericQ[xPeriod\[Vee]s],
one=Table[1,{nyGrid\[Vee]s+1}];
xx=Append[px,N[xPeriod\[Vee]s one,prec]]//Flatten;
yy=Append[py,py[[1]]]//Flatten;
zz=Append[pz,pz[[1]]]//Flatten;];
If[NumericQ[yPeriod\[Vee]s],
one=Table[1,{nxGrid\[Vee]s+1}];
xx=Append[px\[Transpose],px\[Transpose][[1]]]\[Transpose]//Flatten;
yy=Append[py\[Transpose],N[yPeriod\[Vee]s one,prec]]\[Transpose]//Flatten;
zz=Append[pz\[Transpose],pz\[Transpose][[1]]]\[Transpose]//Flatten;];
Interpolation[{{xx,yy}\[Transpose],zz}\[Transpose],opt]]];


Options[interpF]={derivQ->False};
interpF[f_[x_?AtomQ],s_String:"",suf_String:"f",opt:OptionsPattern[]]:=Module[{lft,rt},
lft={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]x\[Diamond]x}//ReleaseHold;
rt={f,f\[Diamond]x,f\[Diamond]x\[Diamond]x}//ReleaseHold;
If[OptionValue[derivQ]==True,MapThread[hold[#1=interp[x,#2,s]]&,{lft,rt}],MapThread[hold[#1=interp[x,#2,s]]&,{{lft[[1]]},{rt[[1]]}}]]];
interpF[f_[x_?AtomQ,y_?AtomQ],s_String:"",suf_String:"f",opt:OptionsPattern[]]:=Module[{lft,rt},
lft={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]x,f\[Diamond]suf\[Diamond]y\[Diamond]y}//ReleaseHold;
rt={f,f\[Diamond]x,f\[Diamond]y,f\[Diamond]x\[Diamond]y,f\[Diamond]x\[Diamond]x,f\[Diamond]y\[Diamond]y}//ReleaseHold;
If[OptionValue[derivQ]==True,MapThread[hold[#1=interp[x,y,#2,s]]&,{lft,rt}],MapThread[hold[#1=interp[x,y,#2,s]]&,{{lft[[1]]},{rt[[1]]}}]]];
interpF[flist_List,s_String:"",suf_String:"f",opt:OptionsPattern[]]:=interpF[#//Flatten,s,suf,opt]&/@flist//Flatten;


itfLinearize[{flist_,reflist___},itfprerepl_,s_String:""]:=Module[{itfprereplh,strtemp,listtemp,mattemp,itflinearize},
itfprereplh=hold[itfprerepl];
strtemp=Map[toString,itfprereplh,{2}]//release;
listtemp=strtemp[[2;;]];
mattemp=StringReplace[listtemp,"list"->"mat"];
itfrepl\[Diamond]s\[DotEqual]unmap@toHeldExpression[{strtemp[[1]],Sequence@@mattemp}];
itflinearize=Join[{ToExpression[listtemp]},{listtemp},{mattemp}]\[Transpose];
eqLinearize[{flist,reflist},itflinearize,s];];
SetAttributes[itfLinearize,HoldAll];


linearMap[{x1_,x2_}->{y1_,y2_}]:=((#-x1) (y2-y1)/(x2-x1)+y1)&;
linearMap[{y1_,y2_}]:=linearMap[{-1,1}->{y1,y2}];
linearMap[x_,{x1_,x2_}->{y1_,y2_}]:=linearMap[{x1,x2}->{y1,y2}][x];
linearMap[x_,{y1_,y2_}]:=linearMap[{y1,y2}][x];


listFormat[m_List,n__]:=Map[Table[1,Evaluate[Sequence@@Partition[Dimensions[m[[n]]],1]]]#&,m,{Length[{n}]}];


listPart[x_List,spec__]:=x[[spec]];


map[heads_List,vars_]:=Map[#[Sequence@@vars]&,heads];


memory:={memoryForm[MemoryInUse[]]<>" in use",memoryForm[MemoryAvailable[]]<>" available"};


memoryForm[mem_,n_:3]:=Which[10^3<=mem<10^6,ToString@NumberForm[N[10^-3 mem],n]<>"\[ThinSpace]K",10^6<=mem<10^9,ToString@NumberForm[N[10^-6 mem],n]<>"\[ThinSpace]M",10^9<=mem<10^12,ToString@NumberForm[N[10^-9 mem],n]<>"\[ThinSpace]G",True,ToString[mem]];


noInfinity[expr_]:=Quiet[expr]/.{Indeterminate->0,ComplexInfinity->0};
SetAttributes[noInfinity,HoldAll];


noSimplify[expr_,lev_:1]:=Block[{Simplify,FullSimplify},Simplify=Identity;If[lev==2,FullSimplify=Identity;];expr];
SetAttributes[noSimplify,HoldFirst];


optimize[expr_]:=Experimental`OptimizeExpression[expr];


periodicAppend[mat_]:=Module[{mattr},mattr=Append[mat,mat[[1]]]\[Transpose];Append[mattr,mattr[[1]]]\[Transpose]];


perturb[f_,dim_Integer:1,s0_String:"0",s1_String:"\[Delta]",ep_:\[Epsilon]]:=Which[dim==1,f->(Evaluate[(f\[Diamond]s0)[#]+ep (s1\[Diamond]f)[#]]&),
dim==2,f->(Evaluate[(f\[Diamond]s0)[#1,#2]+ep (s1\[Diamond]f)[#1,#2]]&),
dim==3,f->(Evaluate[(f\[Diamond]s0)[#1,#2,#3]+ep (s1\[Diamond]f)[#1,#2,#3]]&)]//ReleaseHold;
SetAttributes[perturb,Listable];


preLinearize[{flist_List,reflist___List},s_String:""]:=(prelinearize={{flist,reflist},s};
nEq\[Diamond]s\[DotEqual]Length[flist];
replrule\[Diamond]s\[DotEqual](replRule[{flist,reflist}]);
calcfderiv\[Diamond]s\[DotEqual](calcDeriv[flist]//unmap);
calcrefderiv\[Diamond]s\[DotEqual](calcDeriv[reflist]//unmap);
calcfrefderiv\[Diamond]s\[DotEqual](calcDeriv[{flist,reflist}]//unmap);
finterpf\[Diamond]s\[DotEqual](interpF[flist,s]//unmap);
refinterpf\[Diamond]s\[DotEqual](interpF[reflist,s]//unmap);
calcfinterp\[Diamond]s\[DotEqual](calcInterp[flist]//unmap);
calcrefinterp\[Diamond]s\[DotEqual](calcInterp[reflist]//unmap);
vars\[Diamond]s\[DotEqual]Flatten[{List@@flist[[1]],{flist,reflist}/.replrule\[Vee]s,release@derivL[{flist,reflist}]}]; (*variables for Compile*)
solsave\[Diamond]s\[DotEqual]Flatten[{flist/.replrule\[Vee]s,lastGrid\[Vee]s}]; (*save solutions*)
hlist\[Diamond]s\[DotEqual]Unevaluated/@Head/@flist;
hlistf\[Diamond]s\[DotEqual]Unevaluated@@@(Evaluate[Head/@flist]\[Diamond]f);
{{nEq\[Diamond]s,replrule\[Diamond]s,calcfderiv\[Diamond]s,calcrefderiv\[Diamond]s,calcfrefderiv\[Diamond]s,finterpf\[Diamond]s,refinterpf\[Diamond]s,calcfinterp\[Diamond]s,calcrefinterp\[Diamond]s,vars\[Diamond]s,solsave\[Diamond]s,hlist\[Diamond]s,hlistf\[Diamond]s},{calcfref\[Diamond]s,calcbryind\[Diamond]s,calcrefred\[Diamond]s}});


release=ReleaseHold;


replRule[]:={};
replRule[f_[x_?AtomQ]]:={f[x]->f,f'[x]->f\[Diamond]x,f''[x]->f\[Diamond]x\[Diamond]x}//ReleaseHold;
replRule[f_[x_?AtomQ,y_?AtomQ]]:={f[x,y]->f,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]x,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]x\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]x\[Diamond]x,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]y\[Diamond]y}//ReleaseHold;
replRule[f_[x_?AtomQ,y_?AtomQ,z_?AtomQ]]:={f[x,y,z]->f,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]x,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]z,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]x\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]x\[Diamond]z,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]y\[Diamond]z,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]x\[Diamond]x,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]y\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]z\[Diamond]z}//ReleaseHold;
replRule[flist_List]:=replRule[#//Flatten]&/@flist//Flatten;


replInterp[f_[x_?AtomQ],suf_String:"f"]:=Module[{lft,rt},
lft={f[x],f'[x],f''[x]};
rt={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]x\[Diamond]x}//ReleaseHold;
MapThread[Rule,{lft,map[rt,x]}]];
replInterp[f_[x_?AtomQ,y_?AtomQ],suf_String:"f"]:=Module[{lft,rt},
lft={f[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]};
rt={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]x,f\[Diamond]suf\[Diamond]y\[Diamond]y}//ReleaseHold;
MapThread[Rule,{lft,map[rt,{x,y}]}]];
replInterp[flist_List,suf_String:"f"]:=replInterp[#//Flatten,suf]&/@flist//Flatten;


round[x_]:=If[FractionalPart[x]==0,IntegerPart[x],x];
SetAttributes[round,Listable];


ruleToSet:=(HoldForm[##]/.Rule->Set)&;


set[a_List,b_List]:=MapThread[Set,{a,b}];  (*a=Unevaluated/@lista*)
set[a_HoldForm,b_HoldForm]:=Table[Identity@@MapThread[Set,{{a[[i]]},{b[[i]]}}],{i,Length[a]}];  (*a=hold@@Unevaluated/@lista, b=hold@@listb*)


setdir:=SetDirectory[NotebookDirectory[]];


simplify=FullSimplify;


solution=(#/.(y_->f_):>Inactive[Set][y\[Diamond]"sol",y\[Diamond]"sol"\[DotEqual]f])&;


Options[spNDSolve]={calcrefredQ->False,epValue->10^-9,eqlistmatQ->False,iniQ->True,linearQ->False,lsqrQ->False,minPrec->0,"D"->False};
spNDSolve[x_,fx_,nxGrid0_,s_String:"",opt:OptionsPattern[]]:=Block[{interpQ=False,ep=OptionValue[epValue],change=1,df,nprint=1},
If[{fx,nxGrid0}!=lastGrid\[Vee]s,interpQ=True;];  (*If the grid is changed, do interpolation from last result*)
If[interpQ===True,finterpf\[Vee]s//release;];  (*get interpolating function*)
lastGrid\[Diamond]s\[DotEqual]{fx,nxGrid0};
cheb[x,fx,nxGrid0,s,FilterRules[{opt},Options[cheb]]];  (*construct the grid*)
calcbryind\[Vee]s;  (*calculate boundary index*)

Which[OptionValue[iniQ]===True,calcfref\[Vee]s;,
interpQ===True,calcfinterp\[Vee]s//release; calcref\[Vee]s;];  (*initialization for iteration*)
If[OptionValue[calcrefredQ]==False,calcrefderiv\[Vee]s//release;];  (*calculate reference derivative*)

While[change>ep,
If[OptionValue[calcrefredQ]==True,calcrefred\[Vee]s//release;];  (*calculate reference reduction*)
calcfderiv\[Vee]s//release;  (*calculate function derivative*)
If[OptionValue[eqlistmatQ]==True,{eqlist\[Diamond]s,mat\[Diamond]s}\[DotEqual]eqlistmat\[Vee]s[[1]];];
lhs\[Diamond]s\[DotEqual]ArrayFlatten[mat\[Vee]s];
rhs\[Diamond]s\[DotEqual]-Flatten[eqlist\[Vee]s];
bryReplace[bryrepl\[Vee]s//release,s];  (*impose boundary conditions*)
df=If[OptionValue[lsqrQ]==False,LinearSolve,LeastSquares][lhs\[Vee]s,rhs\[Vee]s];
If[OptionValue[linearQ]==True,
set[hlist\[Vee]s,Partition[df,dimGrid\[Vee]s]];Break[];];
change=Norm[df];

If[nprint==1,changes={change};nprint++;,AppendTo[changes,change];];
If[change>ep^-1,Print["change>",ep^-1];Abort[];];

addTo[hlist\[Vee]s,Partition[df,dimGrid\[Vee]s]];];
output];
spNDSolve[x_,fx_,nxGrid0_,plists__List,s_String:"",opt:OptionsPattern[]]:=Block[{n=1,out},
continue[out=spNDSolve[x,fx,nxGrid0,s,iniQ->If[n==1,OptionValue[iniQ],False],opt];If[n==1,outputs={out};n++;,AppendTo[outputs,out];],plists];
Print["Saved to ",Style["outputs",Bold]]];
SetAttributes[spNDSolve,HoldFirst];


Options[spNIntegrate]={minPrec->0};
spNIntegrate[x_,fx_,nxGrid0_,expr_,s_String:"",opt:OptionsPattern[]]:=(cheb[x,fx,nxGrid0,s,FilterRules[{opt},Options[cheb]]];
lhs\[Diamond]s\[Diamond]"="\[Diamond]"d"\[Diamond]x//release;
rhs\[Diamond]s\[DotEqual]expr;
lhs\[Diamond]s[[1]]\[DotEqual]id\[Vee]s[[1]];
rhs\[Diamond]s[[1]]\[DotEqual]0;
LinearSolve[lhs\[Vee]s,rhs\[Vee]s]);
SetAttributes[spNIntegrate,HoldAll];


toHeldExpression=ToExpression[#,StandardForm,HoldForm]&;


toString[x_]:=ToString[Unevaluated[x]];
SetAttributes[toString,{HoldAll,Listable}];


unevaluate[expr_]:=Identity@@Identity@@MapAll[Unevaluated,Hold[expr],Heads->True];
SetAttributes[unevaluate,{HoldAll,Listable}];


union=DeleteCases[Union[#],0]&;


unmap[list_,head_:HoldForm]:=head@@Replace[Hold[Evaluate[list]],head[x__]:>x,Infinity];
