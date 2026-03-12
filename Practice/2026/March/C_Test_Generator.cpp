#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void solve()
{
    int s, m;
    cin >> s >> m;
    if((s & 1) and !(m & 1)){
        cout << -1 << endl;
        return;
    }
    vector<int> b;
    for(int i = 60; i >= 0; i--){
        if(m & (1ll << i)){
            b.push_back(i);
        }
    }
    int l = 1, r = 1e18;
    while(l <= r){
        int n = l + (r - l) / 2;
        int ts = s;
        for(auto &x: b){
            int p = (1ll << x);
            int take = ts / p;
            if(take > n)
                take = n;
            ts -= take * p;
        }
        if(ts)
            l = n + 1;
        else
            r = n - 1;
    }
    cout << (l > inf ? -1 : l) << endl;
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