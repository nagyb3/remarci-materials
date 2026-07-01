#include <iostream>
#include <fstream>
#include <vector>
#include "point.h"
#include "circle.h"

using namespace std;

int count(const Circle& cir, const vector<Point> &t);
bool search(const Circle& cir, const vector<Point> &t, unsigned int &ind);

int main()
{
	Point origo(0,0);
	
	Circle unitCircle(origo,1);
	
	Point pointA(0,1);
	
	//--------------------------------------------------------------------------------
	
	cout << "Az elso pontunk, az origo: " << origo << endl;
	cout << "A korunk, az egysegkor: " << unitCircle << endl;
	cout << "A masodik pontunk (A): " << pointA << endl;
	
	
	//--------------------------------------------------------------------------------
	
	if (unitCircle.contains(pointA)){
		cout << "Benne van az egysegkorben az A pont" << endl;
	} else {
		cout << "Nincs rajta az egysegkoron az A pont" << endl;
	}
	
	//--------------------------------------------------------------------------------
	
	//1. feladat: kód kiegészítése területet kiszámító függvénnyel (M_PI használható pi helyett)
	//cout << "Az egysegkor terulete " << unitCircle.area() << endl;
	
	//--------------------------------------------------------------------------------
	
	ifstream f("input.txt");
	if(f.fail()) cout << "Hibas fajl nev!\n";

	try{
		Circle cir;
		f >> cir;

		//Alternatív megoldás:
		//double a, b, c;
		//f >> a >> b >> c;
		//Circle cir(Point(a,b),c);
		
		vector<Point> points;
		Point tmp;
		while(f >> tmp){
			points.push_back(tmp);
		}

		// számlálás
		cout << "A kor lemezere eso pontok szama: " << count(cir, points) << endl;


		// lineáris keresés
		unsigned int ind;
		if(search(cir, points, ind)) {
			cout << "A (" << points[ind].getX() << "," << points[ind].getY() << ") koordinataju pont a korlemezre esik\n";
		} else {
			cout << "Egyik pont sincs a korben\n";
		}

	}catch(Circle::WrongRadiusException ex){
		cout << "Kor sugara nem lehet negativ!\n";
	}
	return 0;
}

int count(const Circle& cir, const vector<Point> &t)
{
	int c = 0;
	for(unsigned int i=0; i<t.size(); ++i)
	{
		if(cir.contains(t[i])) ++c;
	}
	return c;
}


//2. feladat: keresés megvalósítása (Melyik az első pont, amely rajta van a lemezen?)
bool search(const Circle& cir, const vector<Point> &t, unsigned int &ind)
{
	//TODO
	return false;
}
