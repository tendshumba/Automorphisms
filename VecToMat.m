
VecToMat:=function(v)
	 return Matrix(BaseField(Parent(v)),[Eltseq(v)]);
end function;
