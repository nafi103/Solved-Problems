#pragma GCC target("popcnt")
#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

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

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

void solve()
{
    char x;
    int n, len;
    cin >> n >> len;
    int a[n];
    memset(a, 0, sizeof a);
    for(int i = 0; i < n; i++){
        for(int j = 0; j < len; j++){
            cin >> x;
            if(x == '1')
                a[i] |= (1 << j);
        }
    }
    int ans = len;
    for(int i = 0; i < n; i++){
        for(int j = i + 1; j < n; j++){
            ans = min(ans, __builtin_popcount(a[i] ^ a[j]));
        }
    }
    cout << ans << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}