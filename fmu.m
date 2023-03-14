
 EigsMinusOne:=[0,1/4,1/32];
fmu:=function(mu)
	 return &*[Polynomial(Rationals(),[-x,1]):x in EigsMinusOne|x ne mu]; 
end function;
