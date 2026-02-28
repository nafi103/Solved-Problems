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
    int n, save;
    cin >> n;
    save = n;
    vector<pair<int,int>> pf;
    for(int i = 2; i * i <= n; i++){
        if(n % i == 0){
            int cnt = 0;
            while(n % i == 0){
                n /= i;
                cnt++;
            }
            pf.push_back({i, cnt});
        }
    }
    if(n > 1)
        pf.push_back({n, 1});
    int k = 1;
    for(auto &[f, s]: pf){
        k *= pow(f, (s + save - 1) / save);
    }
    cout << k << endl;
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