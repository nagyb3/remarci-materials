expanded class --Extra: expanded class
	MAYBE [T]

inherit --Extra: required because of expanded class
	ANY
		rename default_create as nothing
		redefine nothing
		end

create
	nothing,
	just

feature
	has: BOOLEAN

	item: attached T
	require
		has_item: has
	do
		check attached value as attached_value then
			Result := attached_value
		end
	ensure --Extra: add missing ensure
		frame: strip() ~ old strip()
	end

feature {NONE}
	value: detachable T

	nothing
	do
		has := False
	ensure then --Extra: ensure **then** is needed for redifinitions
		no_item: not has
	end

	just(v: attached T)
	do
		has := True
		value := v
	ensure
		has_item: has
		correct_item: item = v
	end

feature --Extra: mutating and pure methods
	orTryFill(new_value: detachable T)
	do
		if not has and attached new_value as attached_new then
			has := True
			value := attached_new
			--Or: just(attached_new)
		end
	ensure
		stability: (old has or new_value = Void) implies strip() ~ old strip()
		if_change: (not old has and new_value /= Void) implies (has and then item = new_value)
	end

	orTryFilled alias "||" (new_value: detachable T): attached MAYBE[T]
	do
		if has then
			create Result.just(item)
		elseif attached new_value as attached_new then
			create Result.just(attached_new)
		else
			create Result.nothing
		end
	ensure
		frame: strip() ~ old strip()
		if_has_item: has implies (Result.has and then Result.item = item)
		if_not_item: not has implies (Result.has = attached new_value
		                              and (Result.has implies Result.item = new_value))
	end

invariant
	has implies attached value

end
