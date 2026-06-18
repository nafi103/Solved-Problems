#include<bits/stdc++.h>
using namespace std;
 #define inf 1e9
 struct SegmentTree {
    vector<int> tree;
    int n;
     SegmentTree(int size)
    {
        n = size;
        tree.resize(4 * n, 0);
    }
     int query(int qs, int qe)
    {
        return queryTree(1, 0, n - 1, qs, qe);
    }
     int queryTree(int index, int s, int e, int qs, int qe)
    {
        if (qs > e || s > qe)
            return 0;
        if (s >= qs && e <= qe)
            return tree[index];
        int m = (s + e) / 2;
        int left_ans = queryTree(2 * index, s, m, qs, qe);
        int right_ans = queryTree(2 * index + 1, m + 1, e, qs, qe);
        return max(left_ans, right_ans);
    }
     void update(int pos, int val)
    {
        updateTree(1, 0, n - 1, pos, val);
    }
     void updateTree(int index, int s, int e, int pos, int val)
    {
        if (pos < s || pos > e)
            return;
        if (s == e) {
            tree[index] = val;
            return;
        }
        int m = (s + e) / 2;
        updateTree(2 * index, s, m, pos, val);
        updateTree(2 * index + 1, m + 1, e, pos, val);
        tree[index] = max(tree[2 * index], tree[2 * index + 1]);
    }
};
 vector<vector<int>>t;
vector<int>values;
vector<int>ans;
int r;
 void dfs(int node, SegmentTree &st){
 int val = values[node];
 int prev_value = st.query(val, val);
 int new_value = st.query(0, val - 1) + 1;
 ans[node] = max(new_value, st.query(0, r+5));
 st.update(val,new_value);
 for(auto &x: t[node]){
  dfs(x,st);
 }
 st.update(val,prev_value);
}
 int main(){
 ios_base::sync_with_stdio(0), cin.tie(0), cout.tie(0);
 int n;
 cin>>n;
 ans.resize(n+1);
 t.resize(n+1);
 for(int i = 2; i<=n; i++){
  int p;
  cin>>p;
  t[p].push_back(i);
 }
 values.resize(n+1);
 set<int>s;
 for(int i = 1; i<=n; i++){
  cin>>values[i];
  s.insert(values[i]);
 }
 map<int,int>mp;
 for(auto &x: s){
  mp[x] = mp.size() + 1;
 }
 for(int i = i; i<=n; i++){
  values[i] = mp[values[i]];
 }
 r = mp.size()+1;
 SegmentTree st(r+10);
 dfs(1,st);
 for(int i = 2; i<=n; i++){
  cout<<ans[i]<<" ";
 }
 cout<<endl;
}