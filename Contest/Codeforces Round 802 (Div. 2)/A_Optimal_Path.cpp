#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int rs = 2, cs = 1, re, ce;
    long long cnt = 0;
    cin >> re >> ce;
    for (cs; cs <= ce; cs++)
        cnt += cs;
    for (rs; rs <= re; rs++)
        cnt += (rs - 1) * ce + ce;
    cout << cnt << endl;
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}