#pragma once
#include <cmath>

class Point
{
	private:
		double _x, _y;
	public:
		Point(double a = 0, double b = 0) : _x(a),_y(b) {}

		double getX() const { return _x;}
		double getY() const { return _y;}

		double distance(const Point &p) const {
			return sqrt(pow(_x-p._x,2) + pow(_y-p._y,2));
		}
		friend std::istream& operator>>(std::istream& is, Point& p)
		{
			is >> p._x >> p._y;
			return is;
		}
		
		friend std::ostream& operator<<(std::ostream& os, const Point& p)
		{
			os << "(" << p._x << "," << p._y << ")";
			return os;
		}
};

