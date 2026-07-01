#pragma once
#define _USE_MATH_DEFINES
#include "point.h"

class Circle
{
	private:
		Point _c;
		double  _r;
	public:
		class WrongRadiusException : public std::exception {};
		Circle(){}
		Circle(const Point &p, double d) : _c(p), _r(d) { if(d<0) throw WrongRadiusException(); }

		bool contains(const Point &p) const {
			return _c.distance(p) <= _r;
		}
		
		friend std::istream& operator>>(std::istream& is, Circle& c)
		{
			is >> c._c >> c._r;
			return is;
		}
		
		friend std::ostream& operator<<(std::ostream& os, const Circle& c)
		{
			os << "Kozeppont: " << c._c << ", sugar: " << c._r;
			return os;
		}
};
