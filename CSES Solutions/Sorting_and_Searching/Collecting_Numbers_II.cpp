#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
int n,q;

int change_now(int i, vector<bool>&contribution,vector<int>&id){
    if(contribution[i]==false){
        if(id[i]<id[i-1]){
            contribution[i]=true;
            return 1;
        }
        return 0;
    }else{
        if(id[i]>id[i-1]){
            contribution[i] = false;
            return -1;
        }
        return 0;
    }
}

int change(int i, vector<bool>&contribution,vector<int>&id){
    int ans = 0;
    if(i>1) ans+=change_now(i,contribution,id);
    i++;
    if(i<=n) ans+=change_now(i,contribution,id);
    return ans;
}


void solve()
{
    cin>>n>>q;
    vector<int>v(n+1),id(n+1);
    for(int i = 1; i<=n; i++){
        cin>>v[i];
        id[v[i]] = i;
    }
    int ans = 1;
    vector<bool> contribution(n+1,false);
    contribution[1] = true;
    for(int i = 2; i<=n; i++){
        if(id[i]<id[i-1]){
            ans++;
            contribution[i] = true;
        }
    }
    while(q--){
        int i,j;
        cin>>i>>j;
        swap(v[i],v[j]);
        id[v[i]]=i;
        id[v[j]]=j;
        ans+=change(v[i],contribution,id);
        ans+=change(v[j],contribution,id);
        cout<<ans<<endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}