# VerKer
ACSL specifications for linux kernel functions

Проект по разработке спецификаций и формальному доказательству корректности библиотечных функций ядра Linux.

# Proofs Status

| ID | Function      | Status | Logic function | libfuzzer | Main | Comment |
|----|---------------|--------|----------------|-----------|------|---------|
| 1  | check\_bytes8 | proved | proved         | yes       | yes  |         |
| 2  | match\_string |        | not required   |           | no   |         |
| 3  | memchr        | proved |                | yes       | yes  |         |
| 4  | memcmp        | proved |                | yes       | no   |         |
| 5  | memscan       | proved | not required   | yes       | yes  |         |
| 6  | skip\_spaces  | proved | proved         | yes       | yes  | requires too strict (remove strlen) |
| 7  | strcasecmp    | proved |                | yes       | no   |         |
| 8  | strcat        | proved | not required   |           | yes  | usr strcmp in ensures |
| 9  | strchr        | proved | proved         | yes       | yes  |         |
| 10 | strchrnul     | proved | proved         | yes       | yes  |         |
| 11 | strcmp        | proved |                | yes       | yes  |         |
| 12 | strcpy        | proved | not required   |           | yes  | use strcmp logic function |
| 13 | strcspn       | proved | proved         | yes       | no   |         |
| 14 | strim         |        | not required   | !const    | no   |         |
| 15 | strlen        | proved | proved         | yes       | yes  |         |
| 16 | strncasecmp   |        |                | yes       | no   |         |
| 17 | strncat       |        | not required   |           | yes  |         |
| 18 | strnchr       | proved |                | yes       | yes  |         |
| 19 | strncmp       |        |                | yes       | yes  |         |
| 20 | strncpy       |        | not required   |           | no   |         |
| 21 | strnlen       | proved | proved         | yes       | yes  |         |
| 22 | strnstr       |        |                | yes       | no   |         |
| 23 | strpbrk       | proved | proved         | yes       | no   |         |
| 24 | strrchr       | proved |                | yes       | yes  |         |
| 25 | strreplace    |        | not required   | !const    | yes  |         |
| 26 | strsep        | proved | not required   | !const    | no   |         |
| 27 | strspn        | proved | proved         | yes       | no   |         |
| 28 | strstr        |        |                | yes       | yes  |         |
| 29 | sysfs\_streq  |        |                | yes       | yes  |         |
| 30 | strlcat       |        | not required   |           | yes  |         |
| 31 | strlcpy       | proved | not required   |           | no   | use strncmp lf in in ensures |
| 32 | memmove       | proved | not required   |           | no   | use memcmp logic function at ensures |
| 33 | memcpy        | proved | not required   |           | no   | use memcmp logic function at ensures |
| 34 | memset        | proved | not required   | !const    | yes  |         |
| 35 | kstrtobool    | proved | not required   | yes       | yes  |         |
| 36 | \_parse\_integer\_fixup\_radix | proved | not required | yes | no | |
| 37 | \_parse\_integer |     |                | yes       | no   |         |

# Toolchain

Спецификации разрабатываются на языке ACSL. В качестве инструментов формальной верификации используются Frama-C с плагином дедуктивной верификации jessie.
- Описание, как установить инструменты можно найти по [ссылке](https://forge.ispras.ru/projects/astraver/wiki). Инструменты работают на Linux, Windows, Mac OS X.
- По [ссылке](https://www.dropbox.com/s/45sjzvfakz2n316/verification.ova?dl=0) можно загрузить образ виртуальной машины VirtualBox в формате ova с уже с предустановленными и настроенными инструментами. Размер образа ~3.6 гигабайт. Ос - Ubuntu. Логин - user. Пароль - 1. В директории **workspace** находятся два репозитория. Один соответствует данному, второй - acsl-proved (примеры с протоколами верикации).

# Repository files

Каждая библиотечная функция ядра Linux располагается в отдельном *.c файле. В соответствующем *.h файле находятся объявления, типы, структуры, специфичные для данной функции.
- В **kernel_definitons.h** файле находятся общие для всех функции типы, макросы и прочие декларации.
- В **ctype.h** находятся сразу несколько функций, которые изначально в ядре были макросами. Для удобства формальной верификации данные макросы (islower,isupper,isdigit,...) были переписаны как inline функции.

# How to add function in repository

В [репозитории](https://github.com/evdenis/spec-utils/) есть инструмент dismember. Он используется для того, чтобы "выцепить" код функции в отдельный файл.
Пример (код для функции strim):
```
$ dismember -m ~/linux-stable/lib/string.c -k ~/linux-stable --double -f strim --output-dir .
```
Будет сформировано два файла: strim.c и strim.h
* Опция **-m** - путь к файлу с определением функции.
* Опция **-k** - путь к директории ядра.
* Опция **--double** - формировать два файла *.h и *.c
* Опция **--f** - имя функции
* Опция **--output-dir** - директория для вывода файлов

# Specifications

Контракт (предусловие и постусловие) находятся для каждой доказанной функции в соответствующем заголовочном файле (например, strlen.h). В нем же находятся леммы/аксиомы/логические функции, если они разработаны для соответствующей функции.

В *.c файле находится тело функции с инвариантами циклов, оценочными функциями и ассертами.

Для некоторых функций спецификации избыточны и фактически дважды по разному описывают то, как функций должна функционировать. Например, одна из таких функций - strlen. В её спецификации есть обычные функциональные требования и есть требование на соответствие возвращаемого результата вызову логической функции под тем же названием strlen. Чем мотивирована подобная "избыточность"? Логическую функцию strlen удобно использовать в спецификациях других функций, например, strcmp (а логическую функции, описывающую поведение функции strcmp при описании функциональных требований к strcpy). При этом все основные свойства логической функции выражаются через леммы (леммы на данном этапе не доказываются). Такие спецификации невозможно отобразить в проверки времени исполнения E-ACSL. Поэтому для тех функций, которым в спецификациях ставится в соответствие логическая функция, обязательно есть и "обычные" спецификации.

Как выбирается будет ли для функции разработана такая избыточная спецификация?
1) Обычной функции можно сопоставить логическую функцию (один-в-один), только если функция на языке Си "чистая" (pure).
2) Логическую функцию рационально писать в том случае, если они пригодится для разработки спецификаций в том числе и для других функций. Например, в функциональных требованиях к memcpy можно выразить "одинаковость" src и dest посредством вызова логической функции memcmp.

Протоколы доказательств (запусков солверов) на текущий момент в репозиторий не включены. Это будет сделано чуть позже, когда будет доказано большее количество функций. На текущий момент, когда спецификации ещё дорабатываются, это лишь "замусорит" репозиторий огромным количеством объемных файлов.

На данном этапе корректность лемм в спецификациях никак не доказывалась. Соответственно, в них могут быть ошибки. Леммы будут доказаны на втором этапе, когда все основные спецификации зафиксированы и будут выкладываться протоколы доказательств. Корректность лемм будет доказана посредством Coq или же лемма-функций, поддерка которых появится в одном из следующий релизов инструментария.

# How to run instruments

```
$ frama-c -jessie <func>.c
$ frama-c -jessie check_bytes8.c
```
Or
```
$ make verify-<func>
$ make verify-check_bytes8
```

# LibFuzzer integration

[LibFuzzer](http://llvm.org/docs/LibFuzzer.html) - библиотека для фаззинга функций. Для части  функций произведена соответствующая интерграция с данной библиотекой. Для того, чтобы можно было запустить фаззинг, необходио иметь в системе компилятор clang, а в корне директоии библиотеку libFuzzer.a
Запуск фаззинга:
```
$ make fuzz-<func>
$ make fuzz-check_bytes8
```
