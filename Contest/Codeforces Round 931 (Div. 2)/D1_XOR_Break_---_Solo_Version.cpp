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
 int msb(int n){
    if(n == 0)
        return -1;
    return 63ll - __builtin_clzll(n);
}
 void solve()
{
    int n, m;
    cin >> n >> m;
    vector<int> ans = {n};
    if(msb(n) != msb(m)){
        int first_diff = -1;
        for(int i = msb(n) - 1; i >= 0; i--){
            if((n & (1ll << i)) == 0 and (m & (1ll << i)) != 0){
                cout << -1 << endl;
                return;
            }
            if((n & (1ll << i)) > 0){
                first_diff = i;
                break;
            }
        }
        int curr = (1ll << msb(n));
        for(int i = first_diff - 1; i >= 0; i--){
            if((n & (1ll << i)) == 0)
                curr |= (1ll << i);
        }
        ans.push_back(ans.back() ^ curr);
        curr = 0;
        for(int i = first_diff; i >= 0; i--){
            if((m & (1ll << i)) == 0)
                curr |= (1ll << i);
        }
        if(curr != 0)
            ans.push_back(ans.back() ^ curr);
        cout << sz(ans) - 1 << endl;
        for(auto &x: ans){
            cout << x << " ";
        }
        cout << endl;
    }else{
        int curr = 0;
        for(int i = msb(n) - 1; i >= 0; i--){
            if((n & (1ll << i)) != (m & (1ll << i)))
                curr |= (1ll << i);
        }
        ans.push_back(ans.back() ^ curr);
        cout << sz(ans) -1 << endl;
        for(auto &x: ans){
            cout << x << " ";
        }
        cout << endl;
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