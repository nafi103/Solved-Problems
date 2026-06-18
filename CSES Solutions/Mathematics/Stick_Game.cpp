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
    int n, k;
    cin >> n >> k;
    int p[k];
    for(int i = 0; i < k; i++)
        cin >> p[i];
    sort(p, p + k);
    bool g[n + 1];
    memset(g, 0, sizeof g);
    for(int i = 0; i < n; i++){
        if(g[i] == 0)
            for(int j = 0; j < k and i + p[j] <= n; j++)
                g[i + p[j]] = 1;
    }
    for(int i = 1; i <= n; i++)
        cout << (g[i] ? 'W' : 'L');
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}