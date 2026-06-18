#include<bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int n,cnt = 0;
        cin>>n;
        int arr[n];
        for (int i = 0; i < n; i++)
        {
            cin>>arr[i];
        }
        int p1,p2;
        p1 = 0;
        p2 = n-1;
        while(p1<p2){
            while(arr[p1]==0&&p1<p2){
                p1++;
            }
            while(arr[p2]>0&&p1<p2){
                p2--;
            }
            if(arr[p1]==1&&arr[p2]==0){
                cnt++;
                p1++;
                p2--;
            }
        }
        cout<<cnt<<endl;
    }
}