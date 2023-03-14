
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// This function computes the orbits of a Miyamoto group given as a matrix group on a list of axes.          +
//It takes as input the MiyamotoGroup and a list of axes.                                                    +                                                           +
//                                                                                                           +
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
MiyamotoOrbits:=function(Grp,lst) 
orbs:=[];
Aut:=Grp;
while #lst gt 0 do
	S:=A`W!Eltseq(lst[1])^Aut;
	S:={@A!Eltseq(x):x in S@};
	Append(~orbs,S);
	lst:=[x:x in lst|x notin S]; 
end while; 
return orbs;
end function;
