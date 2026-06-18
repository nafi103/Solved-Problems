#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
 using namespace std;
using namespace chrono;
using namespace __gnu_pbds;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 int msb(int x){
    return 31-__builtin_clz(x);
}
 void solve()
{
    int n,q;
    cin>>n>>q;
    vector<int>v(n+1,0),pref_xor(n+1,0);
    vector<vector<int>>bit_pos(30);
    for(int i = n; i>=1; i--){
        cin>>v[i];
    }
    for(int i = 1; i<=n; i++){
        for(int j = 0; j<30; j++){
            if((v[i]&(1ll<<j))) bit_pos[j].pb(i);
        }
        pref_xor[i] = (v[i]^pref_xor[i-1]);
    }
    while(q--){
        int x,last = 0;
        cin>>x;
        while(last<n and x>0){
            int curr_msb = msb(x);
            int pos = n;
            for(int j = curr_msb; j<30; j++){
                if(bit_pos[j].empty()) continue;
                int len = sz(bit_pos[j]);
                int nxt = upper_bound(all(bit_pos[j]),last) - bit_pos[j].begin();
                if(nxt<len) pos = min(pos,bit_pos[j][nxt]);
            }
            pos--;
            x = (x^(pref_xor[pos]^pref_xor[last]));
            pos++;
            if(v[pos]>x){
                cout<<pos-1<<" ";
                break;
            }else{
                x=(x^v[pos]);
                last = pos;
            }
        }
        if(last==n or x==0) cout<<last<<" "; 
    }
    cout<<endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}