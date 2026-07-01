//Készítette:    Veszprémi Anna
//Dátum:         2019.02.19.
//Menürendszer forráskód
//Feladat:       A menüpontok a prioritásos sor típus műveleteit meghívják, majd
//               a művelet lefutása után mindig kiírják a sor jellemzőit.
//               Terhelés teszttel vizsgálható a memória kapacitás.

#include <iostream>
#include "menu.h"
#include "read.hpp"
#include <sstream>
#define menudb 4 //egyedul itt kell javitani, ha a menüt bővítjük

using namespace std;

//Ellenőrzéshez 0..menudb kozotti menüpontokat lehet választani
bool check(int a){return a>=0 && a<=menudb;}

void Menu::run()
{
    int v;
    do{
        v = getMenuPoint();
        switch(v){
            case 1:
                putIn();
                break;
            case 2:
                removeMax();
                break;
            case 3:
                getMax();
                break;
            case 4:
                checkEmpty();
                break;
            default:
                cout<<"\nViszontlatasra!\n";
                break;
        }
    }while(v!=0);
}

int Menu::getMenuPoint()
{
    int v;
    cout << "\n****************************************\n";
    cout << "0. Kilepes\n";
    cout << "1. Prior sorba berak\n";
    cout << "2. Legnagyobbat kivesz\n";
    cout << "3. Legnagyobbat lekerdez\n";
    cout << "4. Ures-e vizsgalat\n";
    cout << "****************************************\n";
    //hiba üzenet rugalmas előállítása
    ostringstream s;
    s << "0 es " << menudb << " kozotti egesz szam legyen!";
    string errmsg=s.str();
    //beolvasás read.hpp segítségével
    v=read<int>("Valasztas:",errmsg,check);

    return v;
}

void Menu::putIn()
{
    Item e;
    cout << "Mit tegyunk be?\n";
    cout << "Prioritas:"; cin >> e.pr;
    cout << "Adat:"; cin >> e.data;
    pq.add(e);
}

void Menu::removeMax()
{
    Item e;
    try{
        e=pq.remMax();
        cout << "Kivett elem:\n" << '(' << e.pr << ", " << e.data << ')' << endl;
    }catch(PrQueue::PrQueueEmpty*){
            cerr << "A kiveves nem sikerult! A pr.sor ures!\n";
    }
}

void Menu::getMax()
{
    Item e;
    try{
        e=pq.getMax();
        cout << "Legnagyobb elem:\n" << '(' << e.pr << ", " << e.data << ')' << endl;
    }catch(PrQueue::PrQueueEmpty*){
            cerr << "A kiveves nem sikerult! A pr.sor ures!\n";
    }
}

void Menu::checkEmpty()
{
    if(pq.isEmpty())
        cout << "A pr.sor ures.\n";
    else
        cout << "A pr.sor nem ures.\n";
}



