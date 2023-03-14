/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function takes an algebra A (dim n) and a subalgebra V of dimension m<=n and a vector v in V written as an m-long+
+ vector and returns an m-long vector in A. The result will be axial, though of course it can be changed.               +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
ToBigVec:=function(A,V,v)
	n:=Dimension(A);m:=Dimension(V);
	basV:=Basis(V);
	return &+[v[i]*A!basV[i]:i in [1..m]];
end function;
