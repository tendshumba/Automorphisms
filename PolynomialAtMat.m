/*Given a polynomial p and a matrix M, form p(M).*/
 PolynomialAtMat:=function(p,M)
	 return &+[Coefficients(p)[i]*M^(i-1):i in [1..Degree(p)+1]];
end function;
