#pragma GCC optimize("O3")
#pragma GCC optimize("Ofast")
#pragma GCC optimize ("unroll-loops")
#include<bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;
#define int int64_t
#define Int long long
#define vi vector<int>
#define pr pair<int,int>
#define vs vector<string>
string cdn[]{"NO", "YES"};
const int N = 2e5 + 123;
const int mod = 1e9 + 7;
#define all(x) x.begin(),x.end()
#define f(i, a, b, c) for (int i = a; i < b; i += c)
#define make_unique(x) sort(all(x)); x.resize(unique(all(x)) - x.begin())
typedef tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update> ordered_set;
template <typename T> istream& operator>>(istream& in, vector<T>& a) {for(auto &x : a) in >> x; return in;};
template <typename T> ostream& operator<<(ostream& out, vector<T>& a) {for(auto &x : a) out << x << ' '; return out;};
#ifndef ONLINE_JUDGE
#define dbg(...) cerr << "[" << #__VA_ARGS__ << "]:", debug_out(__VA_ARGS__)
#else 
#define dbg(x) 
#endif
void solve(){
    int n,x;
    cin>>n>>x;
    vi v(n);
    int pos;
    map<int,int>mp;
    for(int i = 0; i<n; i++){
        cin>>v[i];
        if(v[i]==x) pos = i;
        mp[v[i]] = i;
    }
    vector<bool> mark(n+1,false);
    mark[x] = true;
    vector<pair<int,int>> change;
    int l = 0, r = n;
    while(r-l>1){
        int mid = (l+r)/2;
        mark[v[mid]] = true;
        if(pos<mid){
            if(v[mid]<x){
                change.push_back({mid,1});
            }
            r = mid;
        }else{
            if(v[mid]>x) change.push_back({mid,0});
            l = mid;
        }
    }
    cout<<change.size()<<endl;
    for(auto [f,s]: change){
        cout<<f+1<<" ";
        if(s==0){
            int i = 1;
            while(mark[i]) i++;
            mark[i] = true;
            cout<<mp[i]+1<<endl;
        }else{
            int i = n;
            while(mark[n]) i--;
            mark[i] = true;
            cout<<mp[i]+1<<endl;
        }
    }
}
int32_t main(){
    int tc = 1;
    cin >> tc;
    for(int i=1;i<=tc;i++){
        //cout << "Case "<<i<<": ";
        solve();
    }
    return 0;
}