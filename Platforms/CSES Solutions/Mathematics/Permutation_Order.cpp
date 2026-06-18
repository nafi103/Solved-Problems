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
vector<int> fact(21);

void solve()
{
    int t;
    cin>>t;
    if(t==1){
        int n,p;
        cin>>n>>p;
        set<int>s;
        for(int i = 1; i<=n; i++){
            s.insert(i);
        }
        vector<int>ans(n);
        for(int i = 0; i<n; i++){
            int j;
            for(auto &x: s){
                j = x;
                if(fact[sz(s)-1]>=p){
                    break;
                }else{
                    p-=fact[sz(s)-1];
                }
            }
            ans[i] = j;
            s.erase(j);
        }
        writev(ans);
    }else{
        int n;
        cin>>n;
        vector<int>v(n);
        readv(v);
        int ans = 0;
        set<int>s;
        for(int i = 1; i<=n; i++){
            s.insert(i);
        }
        for(int i = 0; i<n; i++){
            for(auto &x: s){
                if(x!=v[i]){
                    ans+=fact[sz(s)-1];
                }else{
                    break;
                }
            }
            s.erase(v[i]);
        }
        cout<<ans+1<<endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    fact[0] = 1;
    for(int i = 1; i<21; i++)
        fact[i] = fact[i-1]*i;
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}