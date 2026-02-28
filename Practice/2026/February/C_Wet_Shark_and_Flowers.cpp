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
    int n, p;
    cin >> n >> p;
    vector<pair<int,int>> range(n);
    for(int i = 0; i < n; i++){
        cin >> range[i].first >> range[i].second;
    }
    double sum = 0;
    for(int i = 0, j = (i + 1) % n; i < n; i++, j = (j + 1) % n){
        auto &[li, ri] = range[i];
        auto &[lj, rj] = range[j];
        double ai = ri / p - (li - 1) / p, aj = rj / p - (lj - 1) / p;
        double p_i = 1.0 - ((ri - li + 1 - ai) / (ri - li + 1)) * ((rj - lj + 1 - aj) / (rj - lj + 1));
        sum += p_i;
    }
    cout << sum * 2000 << endl;
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