#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 vector<int> query(set<int> &available){
    cout << "? " << sz(available);
    for(auto &x: available)
        cout << " " << x;
    cout << endl;
    int len;
    cin >> len;
    vector<int> mono_seq(len);
    for(int i = 0; i < len; i++){
        cin >> mono_seq[i];
        available.erase(mono_seq[i]);
    }
    return mono_seq;
}
 void solve()
{
    int n;
    cin >> n;
    int dp[n * n + 2];
    set<int> available;
    for(int i = 1; i <= n * n + 1; i++)
        available.insert(i);
    for(int i = 1; i <= n; i++){
        vector<int> mono_seq = query(available);
        if(sz(mono_seq) >= n + 1){
            cout << "!";
            for(int i = 0; i <= n; i++)
                cout << " " << mono_seq[i];
            cout << endl;
            return;
        }else{
            for(auto &x: mono_seq)
                dp[x] = i;
        }
    }
    for(auto &x: available)
        dp[x] = n + 1;
    vector<int> ans(n + 1);
    int p = n, target = n + 1;
    for(int j = n * n + 1; p >= 0 and j >= 1; j--){
        if(dp[j] == target){
            target--;
            ans[p] = j;
            p--;
        }
    }
    cout << "!";
    for(int i = 0; i <= n; i++)
        cout << " " << ans[i];
    cout << endl;
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