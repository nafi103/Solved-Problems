#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
int n, fm;
vector<int> dp;
vector<vector<int>> m;

int f(int mask){
    if(mask == fm)
        return 1;

    int &ans = dp[mask];
    if(ans != -1)
        return ans;

    ans = 0;
    int i = __builtin_popcount(mask);
    for(int j = 0; j < n; j++){
        if(mask & (1 << j))
            continue;
        if(m[i][j] == false)
            continue;
        ans = (ans + f(mask | (1 << j))) % mod;
    }

    return ans;
}

void solve()
{
    cin >> n;
    fm = (1 << n) - 1;

    dp.assign(fm, -1);
    m.resize(n, vector<int>(n));

    for(int i = 0; i < n; i++){
        for(int j = 0; j < n; j++){
            cin >> m[i][j];
        }
    }

    cout << f(0) << endl;
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