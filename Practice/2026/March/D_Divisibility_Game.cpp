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
    int n, m, l = 1;
    cin >> n >> m;
    set<int> in_a;
    vector<int> b(m);
    for(int i = 0, x; i < n; i++){
        cin >> x;
        in_a.insert(x);
        if(l <= n + m){
            l = lcm(l, x);
        }
    }
    for(int i = 0; i < m; i++){
        cin >> b[i];
    }
    int acnt = 0, bcnt = 0, both = 0;
    if(l <= n + m){
        for(auto &x: b)
            if(x % l == 0)
                acnt++;
    }
    bool divisible[n + m + 1];
    memset(divisible, 0, sizeof divisible);
    for(auto &x: in_a){
        for(int j = x; j <= n + m; j += x){
            divisible[j] = true;
        }
    }
    for(auto &x: b){
        if(!divisible[x])
            bcnt++;
    }
    both = m - acnt - bcnt;
    acnt += (both + 1) / 2;
    bcnt += (both) / 2;
    if(acnt > bcnt){
        cout << "Alice" << endl;
    }else{
        cout << "Bob" << endl;
    }
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