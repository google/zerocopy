	cmp	xzr, xzr
	mov	x8, #-1
	lsl	w8, w3, w4
	mrs	x9, NZCV
	
	cmp	xzr, xzr
	adds	x8, x3, x4
	mrs	x9, NZCV
	
	cmp	xzr, xzr
	mov	x8, #-1
	add	w8, w3, w4
	mrs	x9, NZCV
	
	cmp	x5, #1
	adcs	x8, x3, x4
	mrs	x9, NZCV
	
	cmp	xzr, xzr
	mov	x8, #-1
	rev	x8, x3
	mrs	x9, NZCV
	
	cmp	xzr, xzr
	mov	x8, #-1
	lsl	x8, x3, x4
	mrs	x9, NZCV
	
	cmp	xzr, xzr
	mov	x8, #-1
	rev	w8, w3
	mrs	x9, NZCV
	