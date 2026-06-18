#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (ll i = (a); i < (b); ++i)
#define rev(i, a, b) for (ll i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl '\n'
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 void solve()
{
    ll r, c, x1, y1, x2, y2, mn = 4;
    cin >> r >> c >> x1 >> y1 >> x2 >> y2;
    if (x1 == 1 || x1 == r)
    {
        if (y1 == 1 || y1 == c)
        {
            cout << 2 << endl;
            return;
        }
        else
        {
            mn = 3;
        }
    }
    if (y1 == 1 || y1 == c)
    {
        if (x1 == 1 || x1 == r)
        {
            cout << 2 << endl;
            return;
        }
        else
        {
            mn = 3;
        }
    }
    if (x2 == 1 || x2 == r)
    {
        if (y2 == 1 || y2 == c)
        {
            cout << 2 << endl;
            return;
        }
        else
        {
            mn = 3;
        }
    }
    if (y2 == 1 || y2 == c)
    {
        if (x2 == 1 || x2 == r)
        {
            cout << 2 << endl;
            return;
        }
        else
        {
            mn = 3;
        }
    }
    if (mn == 3)
    {
        cout << 3 << endl;
        return;
    }
    else
        cout << 4 << endl;
}
 int main()
{
    fastIO;
    ll t;
    cin >> t;
    while (t--)
        solve();
}