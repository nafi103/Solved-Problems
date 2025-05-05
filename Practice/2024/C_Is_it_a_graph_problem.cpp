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
using vi = vector<int>;
using pii = pair<int,int>;

vector<vector<pii>> inc_exc_numbers;
// pair value {f,s} -> f = the number, if s&1 include else exclude

vector<pii> compute_inc_exc(int num, vector<vi>&primes){
    vector<pii> ans;
    int left_max = sz(primes[num]);
    int n = (1<<left_max);
    for(int i = 1; i<n; i++){
        int cnt = 0, number = 1;
        for(int j = 0; j<left_max; j++){
            if(i&(1<<j)){
                number*=primes[num][j];
                cnt++;
            }
        }
        ans.pb({number,cnt});
    }
    return ans;
}

void precompute(){
    int n = 1e4+5;
    inc_exc_numbers.resize(n);
    vector<vi>primes(n);
    for(int i = 2; i<n; i++){
        if(primes[i].empty()){
            for(int j = i; j<n; j+=i){
                primes[j].pb(i);
            }
        }
        inc_exc_numbers[i] = compute_inc_exc(i,primes);
    }
}

vector<int>parent, _size,value;
vector<unordered_map<int,int>> freq;

int find(int i){
    if(parent[i]==i) return i;
    return parent[i] = find(parent[i]);
}

int size(int a){
    a = find(a);
    return _size[a];
}

void Union(int a, int b){
    a = find(a);
    b = find(b);
    if(a==b) return;
    if(_size[a]<_size[b]) swap(a,b);
    parent[b] = a;
    _size[a]+=_size[b];
    for(auto &[f,s]: freq[b]){
        freq[a][f]+=s;
    }
}

void update(int i, int x){
    int parent = find(i);
    for(auto &[f,s] : inc_exc_numbers[value[i]]){
        freq[i][f]--;
        if(i!=parent) freq[parent][f]--;
    }
    for(auto &[f,s] : inc_exc_numbers[x]){
        freq[i][f]++;
        if(i!=parent) freq[parent][f]++;
    }
    value[i] = x;
}

void query(int i, int n){
    int parent = find(i);
    int gcd_not_one = 0;
    for(auto &[f,s]: inc_exc_numbers[value[i]]){
        if(s&1){
            gcd_not_one+=freq[parent][f];
        }else{
            gcd_not_one-=freq[parent][f];
        }
    }
    cout<<_size[parent] - gcd_not_one<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    precompute();
    int n,m;
    cin>>n>>m;

    value.resize(n+1);
    parent.resize(n+1);
    _size.assign(n+1,1);
    freq.resize(n+1);

    for(int i = 1; i<=n; i++) cin>>value[i];

    for(int i = 1; i<=n; i++){
        parent[i] = i;
        for(auto &[f,s]: inc_exc_numbers[value[i]]){
            freq[i][f]++;
        }
    }

    while(m--){
        int u,v;
        cin>>u>>v;
        Union(u,v);
    }

    int q;
    cin>>q;
    while(q--){
        int type;
        cin>>type;
        if(type==1){
            int i,x;
            cin>>i>>x;
            update(i,x);
        }else if(type==2){
            int i;
            cin>>i;
            query(i,n);
        }else{
            int u,v;
            cin>>u>>v;
            Union(u,v);
        }
    }
}