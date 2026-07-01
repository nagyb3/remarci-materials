---
title: Haladó Java gyakorlati feladatok
css: halado-java-feladatok.css
lang: hu-HU
...

<!-- 
pandoc halado-java-feladatok.md -s --toc --strip-comments -o halado-java-feladatok.html
-->

## Bemelegítő Java feladat

A *TESZT* feliratú részeket egyszerű kipróbáló kódként lehet megírni a főprogramba.

- Még jobb: JUnit 5 tesztelővel meghajtható alakban is elkészíthetők.

Szindbádot, a tengerészt követjük kalandjaira, a Gyémántok Szigetére. Az a terve, hogy összegyűjt néhány gyémántot, majd egy barátságos Ankaa madár elrepíti a szigetről. Szindbád biztonságba érve eltárolja a gyémántjait, majd másnap újra visszatér a szigetre.

### 1. részfeladat

Készítsd el az `exam.sinbad.sky.Bird` interfészt. Ennek `isAtHeightRange()` metódusa egy `height` egész számot kap meg, és egy logikai értékkel tér vissza. Van továbbá egy `getName` metódusa is, ami egy szöveget ad vissza.

Készítsd el az `exam.sinbad.Adventure` osztályt a következő adattagokkal:
`collectedDiamonds` (kezdetben `0`), `birds` (`Bird` típusú elemek listája; a `getBirdCount` művelet visszatér a lista hosszával) és `day`(kezdetben `1`).
Van egy osztályszintű adattagja is: `storedDiamonds`(kezdetben `0`).

- A `collectDiamonds()` és `storeDiamonds()` műveletek egy `diamondCount` egész paramétert kapnak, és ezt hozzáadják a `collectedDiamonds` illetve `storedDiamonds` adattagokhoz.
- A `clearStoredDiamonds()` művelet beállítja `storedDiamonds` értékét nullára.
- A `storeDiamonds()` metódus és mindegyik adattag csak az `Adventure` osztály leszármazottai számára legyen elérhető. Minden adattaghoz legyen getter is.

A kalandot leíró `Adventure` osztálynak két konstruktora legyen:

1. Az egyik tetszőleges számú `Bird` paramétert kaphasson, és ezeket adja hozzá a `birds` listához.
    - Ha a konstruktor háromnál több madarat kap, váltson ki `IllegalArgumentException` kivételt.
2. A másik legyen paraméter nélküli. Ez hívja meg az előző konstruktort egyetlen `BigBird` nevű `Ankaa` madárral, amelynek a `height` értéke `700`.
    - Az `Ankaa` osztály részleteit lásd lent.

TESZT: Készítsd el a `tests.AdventureTest` osztályt, ami JUnit 5-öt használ, és a következőket ellenőrzi külön-külön metódusokba megírt tesztesetekkel.

- Az első konstruktorral készített kalandban kezdetben `0` összegyűjtött gyémánt van.
- A második konstruktorral készített kalandban kezdetben `0` összegyűjtött gyémánt van.
- A kalandokban a megfelelő a `getBirdCount` értéke. Ez `0` és `2` madárral ellenőrizendő.
- A későbbiekben leírt teszteseteket is ebbe az osztályba kell beleírni.

### 2. részfeladat

Az `exam.sinbad.sky.HeightRange` felsorolási típusnak négy értéke legyen: `LOW`, `MEDIUM`, `HIGH` és `BEYOND`.

- Két adattagja van: `min` és `max`.
- Két konstruktora van. Az első egyszerűen átveszi és beállítja `min` és `max` értékét. A második áthív az előzőre, mindkét paraméterben nullát átadva.
- A felsorolási típus első három értéke két paramétert kap, amelyek a `0..300`, `301..600` és `601..900` `min-max` határokat jelölik. A `BEYOND` értékhez nem tartozik paraméter.
- A típus osztályszintű `getHeightRange()` metódusa egy egész számot kap meg. Ez bejárja sorban a felsorolási típus elemeit, és megnézi, hogy a kapott szám beleesik-e `min` és `max` közé. Ha igen, a metódus az éppen érintett felsorolási elemmel tér vissza. Ha a legutolsó `BEYOND` elemig is eljut a bejárás, akkor vizsgálat nem szükséges, azzal tér vissza.
- TESZT: teszteld a `getHeightRange()` metódus visszatérési értékét az alábbi paraméterekkel: `0`, `299`, `300`, `301`, `600`, `601`, `900`, `901`. (Nem szükséges paraméterezett tesztelőt használni, lehet mindegyik külön teszteset.)

Készítsd el az `exam.sinbad.sky.Ankaa` osztályt a `name` és `height` adattagokkal.

- Az utóbbinak legyen settere, és mindkettőnek gettere.
- A `toString()` művelet kimenete ilyen alakú legyen: `ThisIsMyName[flying HIGH at 765 meters]` or `OneDoesNotSimplyFlyOutOfDiamondIsland[flying BEYOND at 100000 meters]`. Használd fel a `HeightRange` felsorolási típust a kimenet elkészítéséhez.

Az `Ankaa` osztály valósítsa meg a `Bird` interfészt.

- Az `isAtHeightRange()` művelet visszatérése adja meg, hogy a madár a paraméterben kapott magassági szinten repül-e. Ehhez azt kell megvizsgálni, hogy a kapott magassághoz tartozó magassági szint megegyezik-e azzal a magassági szinttel, ahol a madár tartózkodik.
- Definiáld felül az `equals()` és a `hashCode()` metódusokat. Az előbbi akkor tekintsen két madarat egyenlőnek, ha azonos magassági szinten (de nem feltétlenül azonos magasságban) repülnek, és megegyezik a nevük.
- TESZT: a `toString()` fenti két példájának megfelelő madár szöveges alakja megfelelő.
- TESZT: azonos adatokkal elkészített két madár egyenlő.
- TESZT: azonos nevű, különböző magasságon (de azonos magassági szinten) repülő két madár egyenlő.
- TESZT: különböző nevű, azonos magasságon repülő két madár *nem* egyenlő.

### 3. részfeladat

Az `Adventure` osztályban készítsd el a `callBird` metódust. Ez egy `height` egészt kap, és megvizsgálja, hogy van-e olyan `Ankaa`, ami az ennek megfelelő szinten száll. Ha van, Szindbádot elviszi a madár: meghívódik rá a `doEscape()`. Különben Szindbád a szigeten marad. A metódus térjen vissza azzal, sikeres volt-e az elmenekülés a szigetről.

- A `doEscape()` legyen elérhető az osztály leszármazottaiban. Paramétere `Bird` típusú. A `collectedDiamonds` értékével meghívja a `storedDiamonds()` műveletet, majd beállítja a `collectedDiamonds` értékét nullára, és megnöveli a `day` értékét.
- TESZT: az első napon, ha egy madár érhető el, és híváskor túl magasan vagy alacsonyan száll, akkor a menekülés sikertelen, és még mindig az első napon járunk.
- TESZT: írj le egy *teljes napig* tartó, sikeres kalandot. Hívj madarat, gyűjts gyémántot, és a `getCollectedDiamonds()`, `getStoredDiamonds()` és `getDay()` segítségével ellenőrizd, hogy minden helyesen történt.
- TESZT: írj le egy *három napig* tartó, sikeres kalandot. Hívj madarat, gyűjts gyémántot, és a `getCollectedDiamonds()`, `getStoredDiamonds()` és `getDay()` segítségével ellenőrizd, hogy minden helyesen történt.
    - Tipp: a tesztelés során a megfelelő ponton meg kell hívni a `clearStoredDiamonds()` metódust.

Készítsd el az `exam.sinbad.ValuableAdventure` osztályt, az `Adventure` gyermekét.

- Az egyetlen konstruktora egy `diamondFilename`-et és tetszőlegesen sok `Bird` elemet kap meg. Ez utóbbiakat át kell adni a szülő konstruktorának.
- Nyisd meg a fájlt (feltételezhető, hogy létezik), és soronként olvasd ki a tartalmát. Minden sor szerkezete ilyen: `BirdName 1234`, ahol a név a madár neve, a szám pedig gyémántok darabszáma.
- Tárold el a madarakhoz tartozó gyémántok darabszámát a `birdDiamonds` adattagban, ami `Map` típusú. Feltételezhető, hogy minden madárhoz csak egyszer van megadva a gyémántok száma.
- A `doEscape()` metódus legyen túlterhelve: a korábban leírt működését hajtsa végre, majd ellenőrizze, hogy a paraméterben megkapott madárhoz tartoznak-e gyémántok a `birdDiamonds` szerint. Ha igen, ezeket a gyémántokat is el kell tárolni (a `storeDiamonds()` segítségével), és a madár kerüljön ki a `birdDiamonds` adatszerkezetből.
