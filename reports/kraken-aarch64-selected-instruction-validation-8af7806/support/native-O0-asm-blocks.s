	cmp	xzr, xzr
	adds	x9, x8, x9
	mrs	x8, NZCV
	
	cmp	x10, #1
	adcs	x9, x8, x9
	mrs	x8, NZCV
	
	cmp	xzr, xzr
	mov	x9, #-1
	add	w9, w8, w10
	mrs	x8, NZCV
	
	cmp	xzr, xzr
	mov	x9, #-1
	lsl	x9, x8, x10
	mrs	x8, NZCV
	
	cmp	xzr, xzr
	mov	x9, #-1
	lsl	w9, w8, w10
	mrs	x8, NZCV
	
	cmp	xzr, xzr
	mov	x9, #-1
	rev	x9, x8
	mrs	x8, NZCV
	
	cmp	xzr, xzr
	mov	x9, #-1
	rev	w9, w8
	mrs	x8, NZCV
	