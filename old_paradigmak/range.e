class
	RANGE

create
	make

feature
	lower, upper: REAL

feature {NONE}
	make(lower_, upper_: REAL)
	require
		lower_le_upper: lower_ <= upper_
	do
		lower := lower_
		upper := upper_
	ensure
		effect: lower = lower_ and upper = upper_
	end

feature
	is_inside(value: REAL): BOOLEAN
	do
		Result := lower < value and value < upper
	ensure
		result_correct: Result = (lower < value and value < upper)
		frame: strip() ~ old strip()
	end

	set_lower(new_lower: REAL)
	require
		lower_le_upper: new_lower <= upper
	do
		lower := new_lower
	ensure
		effect: lower = new_lower
		frame: strip(lower) ~ old strip(lower)
	end

	set_upper(new_upper: REAL)
	require
		lower_le_upper: lower <= new_upper
	do
		upper := new_upper
	ensure
		effect: upper = new_upper
		frame: strip(upper) ~ old strip(upper)
	end

	multiplied_by alias "*" (value: REAL): attached RANGE
	require
		scale_not_negative: value >= 0
	do
		create Result.make(lower * value, upper * value)
	ensure
		correct: Result.lower = lower * value and Result.upper = upper * value
		frame: strip() ~ old strip()
	end

invariant
	lower_le_upper: lower <= upper

end
