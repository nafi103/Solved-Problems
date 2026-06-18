#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
 using namespace std;
using namespace chrono;
using namespace __gnu_pbds;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int N = 2e5 + 10;
int n, k, a[N], b[N], id[N], sc[N], an[N];
 void input(){
    cin >> n >> k;
    for(int i = 0; i < n; i++){
        an[i] = i - 1;
        sc[i] = i + 1;
        cin >> a[i];
        id[a[i]] = i;
    }
    sc[n - 1] = -1;
    for(int i = 0; i < k; i++)
        cin >> b[i];
}
 void solve()
{
    input();
    set<int> rem;
    for(int i = 0; i < k; i++)
        rem.insert(b[i]);
    int ans = 1;
    for(int i = 0; i < k; i++){
        int mul = 0, curr_id = id[b[i]], p = an[curr_id], s = sc[curr_id];
        if(s != -1 and rem.count(a[s]) != 1){
            mul++;
            if(sc[s] != -1)
                an[sc[s]] = curr_id;
        }
        if(p != -1 and rem.count(a[p]) != 1){
            if(!mul){
                if(an[p] != -1)
                    sc[an[p]] = curr_id;
            }
            mul++;
        }
        ans = (ans * mul) % mod;
        if(ans == 0){
            cout << 0 << endl;
            return;
        }
        rem.erase(b[i]);
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}