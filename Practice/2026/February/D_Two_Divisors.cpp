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

const int N = 1e7;
int spf[N+1];
vector<int> pr;

void solve()
{
    vector<pair<int,int>> ans;
    int n;
    cin >> n;
    for(int i = 0; i < n; i++){
        int x;
        cin >> x;
        vector<int> prime_d;
        while(x > 1){
            prime_d.push_back(spf[x]);
            while(x % prime_d.back() == 0)
                x /= prime_d.back();
        }
        if(sz(prime_d) == 1){
            ans.emplace_back(-1, -1);
        }else{
            int x = prime_d[0], y = 1;
            for(auto &z: prime_d)
                y = y * z;
            y /= x;
            ans.emplace_back(x, y);
        }
    }
    for(auto &[f, s]: ans)
        cout << f << " ";
    cout << endl;
    for(auto &[f, s]: ans)
        cout << s << " ";
    cout << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    for (int i = 2; i <= N; ++i) {
        if (spf[i] == 0) {
            spf[i] = i;
            pr.push_back(i);
        }
        for (int j = 0; i * pr[j] <= N; ++j) {
            spf[i * pr[j]] = pr[j];
            if (pr[j] == spf[i]) {
                break;
            }
        }
    }
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}
