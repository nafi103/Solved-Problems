#include <bits/stdc++.h>
using namespace std;
#define Code ios_base::sync_with_stdio(false);
#define By cin.tie(NULL);
#define ll int
ll query(ll x, ll y)
{
    cout << "? " << x << " " << y << endl;
    ll res;
    cin >> res;
    return res;
}
void asquare()
{
    ll n, m;
    cin >> n >> m;
    ll res = query(1, 1);
    ll res2 = 0, res3 = 0;
    ll x2 = 0, y2 = 0, x3 = 0, y3 = 0;
    if (res <= n - 1)
    {
        x2 = res + 1;
        y2 = 1;
    }
    else
    {
        x2 = n; 
        y2 = res - n + 2;
    }

    if (res <= m - 1)
    {
        x3 = 1;
        y3 = res + 1;
    }
    else
    {
        x3 = res - m + 2;
        y3 = m;
    }
    res2 = query(x2, y2)>>1;
    res3 = query(x3, y3)>>1;

    x3 += res3;
    y3 -= res3;
    x2 -= res2;
    y2 += res2;
    ll res4 = query(x3, y3);
    if (res4 == 0)
    {
        cout << "! " << x3 << " " << y3 << endl;
    }
    else
    {
        cout << "! " << x2 << " " << y2 << endl;
    }
}
// Main
int main()
{
    ll t;
    cin >> t;
   while(t--)
    {
        asquare();
    }
    return 0;
}
// End