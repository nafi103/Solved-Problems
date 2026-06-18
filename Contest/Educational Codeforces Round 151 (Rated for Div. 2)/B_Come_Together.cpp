#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define set_bits(x) __builtin_popcount(x)
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "
#define endl "\n"
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 void solve()
{
    ll arr[3][2];
    ll x1, y1, x2, y2, x3, y3;
    cin >> x1 >> y1 >> x2 >> y2 >> x3 >> y3;
    ll xb = x2 - x1, xc = x3 - x1, yb = y2 - y1, yc = y3 - y1;
    if (xb * xc >= 0 && yb * yc >= 0)
    {
        cout << min(abs(xb), abs(xc)) + min(abs(yb), abs(yc)) + 1 << endl;
    }
    else if (xb * xc <= 0)
    {
        if (yb * yc <= 0)
        {
            cout << 1 << endl;
        }
        else
        {
            cout << min(abs(yb), abs(yc)) + 1 << endl;
        }
    }
    else
    {
        if (xb * xc <= 0)
        {
            cout << 1 << endl;
        }
        else
        {
            cout << min(abs(xb), abs(xc)) + 1 << endl;
        }
    }
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}