#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void solve()
{
    int x, y;
    cin >> x >> y;
    int p1 = x, q1 = y, p2 = x, q2 = y;
    while(p1 & q1)
        p1++;
    while(p2 & q2)
        q2++;
    if(abs(p1 - x) + abs(q1 - y) < abs(p2 - x) + abs(q2 - y))
        cout << p1 << " " << q1 << endl;
    else
        cout << p2 << " " << q2 << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}