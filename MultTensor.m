 MultTensor:=function(t,u,v)
	 sols:=Roots(Polynomial(IntegerRing(),[-2*#t,1,1]));
	 d:=[x[1]:x in sols|Sign(x[1]) eq 1][1];
	 if Degree(u) ne d then
		 return Sprintf("error, the vector must be %o long\n",d);
		 else
		 sq:=&+[u[i]*v[i]*t[IntegerRing()!((i-1)/2*(2*d+2-i))+1]:i in [1..d]];
		 rest:=&+[&+[(u[i]*v[j]+u[j]*v[i])*t[IntegerRing()!((i-1)/2*(2*d-i+2))+j-i+1]:i in [1..(d-1)],j in [1..d]|j gt i]];
		 return sq+rest;
		 end if;
end function;

