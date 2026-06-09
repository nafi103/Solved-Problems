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

    int nd = x & y;
    if(nd == 0){
        cout << x << " " << y << endl;
        return;
    }

    int ans_p = -1, ans_q = -1, min_cost = 1e18;

    auto update = [&](int p, int q) {
        if ((p & q) == 0) {
            int cost = abs(x - p) + abs(y - q);
            if (cost < min_cost) {
                min_cost = cost;
                ans_p = p;
                ans_q = q;
            }
        }
    };

    int msb = 63ll - __builtin_clzll(nd);

    int p = x & ~((1ll << msb) - 1);
    int q = (y & ~((1ll << (msb + 1)) - 1)) | ((1ll << msb) - 1);
    update(p, q);

    p = (x & ~((1ll << (msb + 1)) - 1)) | ((1ll << msb) - 1);
    q = y & ~((1ll << msb) - 1);
    update(p, q);

    p = (x & ~((1ll << (msb + 1)) - 1)) + (1ll << (msb + 1));
    q = y;
    update(p, q);

    p = x;
    q = (y & ~((1ll << (msb + 1)) - 1)) + (1ll << (msb + 1));
    update(p, q);

    cout << ans_p << " " << ans_q << endl;
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