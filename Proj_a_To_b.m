/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given two vectors a and b, project a to b. We assume that the axial algebra containing a and b has a definite form U  +
+                                                                                                                       +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 
Proj_aTo_b:=function(a,b,form)  
	return (FrobFormAtElements(a,b,form)/FrobFormAtElements(b,b,form))*b;
end function;
