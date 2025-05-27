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

vector<int>parent, capacity, ini; 

int find(int i){ 
    if(parent[i]==i or capacity[i]) return i; 
    return parent[i] = find(parent[i]); 
}

void Reparent(int node){ 
    int par = find(node);
    if(par==node) return;
    parent[node] = par;
}

void push(int node, int val){
    int mn = min(val,capacity[node]);
    capacity[node]-=mn;
    val-=mn;
    while(val){
        Reparent(node);
        int par = parent[node];
        int mn = min(val,capacity[par]);
        capacity[par]-=mn;
        val-=mn;
    }
}

void solve(){
    int n,q; 
    cin>>n>>q; 
    capacity.resize(n+1);
    parent.resize(n+1); 
    parent[n] = n;
    for(int i = 0; i<n; i++){
        cin>>capacity[i];
    }
    capacity[n] = inf;
    ini = capacity;
    stack<int>st;
    st.push(n);
    for(int i = n-1; i>=0; i--){
        while(capacity[i]>=capacity[st.top()]){
            st.pop();
        }
        parent[i] = st.top();
        st.push(i);
    }
    while(q--){
        char t;
        cin>>t;
        if(t=='+'){
            int id,val;
            cin>>id>>val;
            id--;
            push(id,val);
        }else{
            int id;
            cin>>id;
            id--;
            cout<<ini[id] - capacity[id]<<endl;
        }
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