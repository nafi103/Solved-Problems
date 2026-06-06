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
    int n, k, m;
    cin >> n >> k >> m;
    vector<pair<int,int>> gem(n);
    for(auto &[c, v]: gem)
        cin >> c >> v;

    sort(all(gem), [&](pair<int,int> &a, pair<int,int> &b){
        if(a.second != b.second)
            return a.second > b.second;
        return a.first < b.first;
    });

    set<int> taken_color;
    vector<bool> taken(n, false);

    int ans = 0;
    for(int i = 0; i < n and sz(taken_color) < m; i++){
        auto &[c, v] = gem[i];
        if(taken_color.count(c) == 0){
            taken_color.insert(c);
            ans += v;
            taken[i] = true;
        }
    }

    k -= m;
    for(int i = 0; i < n and k; i++){
        auto &[c, v] = gem[i];
        if(!taken[i]){
            ans += v;
            k--;
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