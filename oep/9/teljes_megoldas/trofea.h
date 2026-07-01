#pragma once

#include "vad.h"


class Trofea {
	public:
		std::string helyszin;
		std::string datum;
		Vad* zsakmany;

		Trofea(const std::string& h, const std::string& d, Vad* zs): helyszin(h), datum(d), zsakmany(zs) {}
};
