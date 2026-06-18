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
    int n, m, q, x;
    cin >> n >> m >> q;
    set<pair<int,int>> present = {{m, m}};
    for(int i = 0; i < q; i++){
        cin >> x;
        set<pair<int,int>> next;
        for(auto &[f, s] : present){
            if(x >= f and x <= s){
                next.insert({1,1});
                next.insert({n,n});
                if(f != s)
                    next.insert({f, s});
            }else if(x < f){
                next.insert({max(f - 1, 1ll), s});
            }else{
                next.insert({f, min(n, s + 1)});
            }
        }
        vector<pair<int,int>> tmp;
        for(auto &[f, s]: next){
            if(tmp.empty() or tmp.back().second + 1 < f){
                tmp.push_back({f, s});
            }else{
                tmp.back().second = s;
            }
        }
        present.clear();
        for(auto &[f, s]: tmp)
            present.insert({f, s});
        int ans = 0;
        for(auto &[f, s]: present){
            ans += s - f + 1;
        }
        cout << ans << (i == q - 1 ? '\n' : ' ');
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